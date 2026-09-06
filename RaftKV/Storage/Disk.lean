/-!
# A disk with realistic crash semantics

The storage proofs rest on a model of the device, and the model has to be
adversarial enough to be honest.

## Three levels, not two

Writing a byte does not make it durable, and there are two distinct steps
between the two — which is exactly the distinction a proof can be tricked into
ignoring. So the model keeps three places a byte can be:

* **buffered** — handed to the process's own buffer. A crash loses it outright;
  the kernel never saw it. This is where `fflush`-less `write` leaves data.
* **cached** — handed to the operating system. A crash may or may not have got
  it to the platter, **independently at each address**. This is where
  `IO.FS.Handle.flush` leaves data, and it is *not* durable.
* **stable** — on the platter. This is what survives.

`flushUser` moves buffered to cached; only `fsync` moves cached to stable. A
commit that flushes but never fsyncs therefore leaves everything at the mercy of
the crash relation, and `Format.flushOnly_not_crash_safe` proves that such a
commit really can come back holding neither the old value nor the new one. The
`fsync` in the commit sequence is load-bearing, and the model is arranged so
that it cannot be quietly dropped.

## What a crash does

Everything buffered is gone. Everything cached may or may not have landed,
independently at each address, which is tearing at byte granularity — and
writes to a single address may land out of order, which is more than any real
device does. Only what was fsynced is certain.

## The one assumption

Nothing can be built on a device where *every* write tears — the commit point
would never be well defined. Real hardware provides a single aligned
sector-sized write that lands entirely or not at all, and this model provides
exactly one such thing: the **root cell**. Everything else is bytes and may
tear. That the device really offers this is the one storage assumption in the
trusted base, and it is stated here rather than buried in an implementation.

## Why the root cell is a type parameter

The commit discipline proved below — *write where the current root cannot see;
flush; fsync; swap the root; flush; fsync* — is copy-on-write in miniature. With
`α := Bool × Nat` it is a two-region superblock, which is what this development
uses. With `α := PageId` it is an LMDB-style copy-on-write B-tree, where the
root cell holds the root page number and `alloc` returns a free page. The
theorem is the same one; only the instance changes.

Addresses are plain `Nat` rather than a named alias: `omega` cannot see through
an `abbrev`, and the layout arithmetic leans on it heavily.
-/

namespace RaftKV.Disk

/--
The device.

`stable` and `root` are what a crash is guaranteed to leave behind. The four
staging lists are what has been written since the last `fsync`, oldest first.
-/
structure Disk (α : Type) where
  /-- Bytes on the platter. -/
  stable : Nat → UInt8
  /-- Bytes handed to the operating system but not yet fsynced. May be lost. -/
  cached : List (Nat × UInt8)
  /-- Bytes still in this process's buffer. Lost on any crash. -/
  buffered : List (Nat × UInt8)
  /-- The root cell on the platter. -/
  root : α
  /-- Root writes handed to the operating system but not yet fsynced. -/
  rootCached : List α
  /-- Root writes still in this process's buffer. -/
  rootBuffered : List α

variable {α : Type}

/-- Overlay a list of byte writes on a base image; later writes win. -/
def overlay (base : Nat → UInt8) : List (Nat × UInt8) → (Nat → UInt8)
  | [] => base
  | (a, v) :: ws => overlay (fun x => if x = a then v else base x) ws

/-- What a read sees: the platter, as overwritten by anything in flight. -/
def Disk.read (d : Disk α) (a : Nat) : UInt8 :=
  overlay (overlay d.stable d.cached) d.buffered a

/-- What a read of the root sees. -/
def Disk.readRoot (d : Disk α) : α :=
  ((d.rootCached ++ d.rootBuffered).getLast?).getD d.root

/--
Write a set of bytes into this process's buffer.

A commit is described by *which addresses get which bytes*, not by a contiguous
run: a copy-on-write B-tree writes a scattered set of pages, and a two-region
superblock writes one run, and both are lists of `(address, byte)`.
-/
def Disk.writeMany (d : Disk α) (ws : List (Nat × UInt8)) : Disk α :=
  { d with buffered := d.buffered ++ ws }

/-- The writes that lay `bs` down starting at `base`. -/
def imgWrites : Nat → List UInt8 → List (Nat × UInt8)
  | _, [] => []
  | a, v :: vs => (a, v) :: imgWrites (a + 1) vs

/-- Write the root cell. This is the one write that cannot tear. -/
def Disk.writeRoot (d : Disk α) (r : α) : Disk α :=
  { d with rootBuffered := d.rootBuffered ++ [r] }

/--
Hand this process's buffer to the operating system.

This is `fflush`, and it is **not** durability: the bytes are now the kernel's
problem rather than ours, but a power cut still loses them.
-/
def Disk.flushUser (d : Disk α) : Disk α :=
  { d with cached := d.cached ++ d.buffered, buffered := [],
           rootCached := d.rootCached ++ d.rootBuffered, rootBuffered := [] }

/--
Force what the operating system holds onto the platter.

This is `fsync`. Note what it does *not* do: it leaves this process's own buffer
alone, exactly as the real call does, which is why `sync` below is the pair.
-/
def Disk.fsync (d : Disk α) : Disk α :=
  { stable := overlay d.stable d.cached, cached := [], buffered := d.buffered,
    root := (d.rootCached.getLast?).getD d.root, rootCached := [],
    rootBuffered := d.rootBuffered }

/-- Make everything written so far durable: flush the buffer, then fsync. -/
def Disk.sync (d : Disk α) : Disk α := d.flushUser.fsync

/-- Read `size` bytes from `base`. -/
def Disk.readRegion (d : Disk α) (base size : Nat) : List UInt8 :=
  (List.range size).map (fun i => d.read (base + i))

/--
**What a crash may reveal.**

Everything buffered is gone: the kernel never saw it. Everything cached may or
may not have reached the platter, independently at each address — that is
tearing, and it is also why a flush without an fsync buys nothing. For the root,
either the old value or one of the cached ones, never a mixture, which is the
atomicity assumption.
-/
def Crash (d d' : Disk α) : Prop :=
  (∀ a, d'.stable a = d.stable a ∨ (a, d'.stable a) ∈ d.cached)
    ∧ (d'.root = d.root ∨ d'.root ∈ d.rootCached)
    ∧ d'.cached = [] ∧ d'.buffered = [] ∧ d'.rootCached = [] ∧ d'.rootBuffered = []

/-- A device with nothing in flight: everything written is on the platter. -/
def Quiet (d : Disk α) : Prop :=
  d.cached = [] ∧ d.buffered = [] ∧ d.rootCached = [] ∧ d.rootBuffered = []

theorem quiet_sync (d : Disk α) : Quiet d.sync := ⟨rfl, rfl, rfl, rfl⟩

theorem crash_quiet {d d' : Disk α} (h : Crash d d') : Quiet d' :=
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- On a quiet device, reads are the platter. -/
theorem read_of_quiet {d : Disk α} (h : Quiet d) (a : Nat) : d.read a = d.stable a := by
  unfold Disk.read; rw [h.1, h.2.1]; rfl

theorem readRoot_of_quiet {d : Disk α} (h : Quiet d) : d.readRoot = d.root := by
  unfold Disk.readRoot; rw [h.2.2.1, h.2.2.2]; rfl

/-- **A crash cannot disturb a device with nothing in flight.** -/
theorem crash_of_quiet {d d' : Disk α} (hq : Quiet d) (h : Crash d d') :
    (∀ a, d'.stable a = d.stable a) ∧ d'.root = d.root := by
  refine ⟨fun a => ?_, ?_⟩
  · rcases h.1 a with hb | hb
    · exact hb
    · rw [hq.1] at hb; exact absurd hb (by simp)
  · rcases h.2.1 with hr | hr
    · exact hr
    · rw [hq.2.2.1] at hr; exact absurd hr (by simp)


/-! ## Reading back what was written -/

theorem overlay_append (base : Nat → UInt8) : ∀ (ws ws' : List (Nat × UInt8)),
    overlay base (ws ++ ws') = overlay (overlay base ws) ws' := by
  intro ws
  induction ws generalizing base with
  | nil => intro ws'; rfl
  | cons w ws ih => intro ws'; cases w; simp only [List.cons_append, overlay]; exact ih _ ws'

theorem overlay_snoc (base : Nat → UInt8) (ws : List (Nat × UInt8)) (a : Nat) (v : UInt8) :
    overlay base (ws ++ [(a, v)]) = fun x => if x = a then v else overlay base ws x := by
  rw [overlay_append]; rfl

@[simp] theorem writeMany_stable (d : Disk α) (ws : List (Nat × UInt8)) :
    (d.writeMany ws).stable = d.stable := rfl
@[simp] theorem writeMany_cached (d : Disk α) (ws : List (Nat × UInt8)) :
    (d.writeMany ws).cached = d.cached := rfl
@[simp] theorem writeMany_buffered (d : Disk α) (ws : List (Nat × UInt8)) :
    (d.writeMany ws).buffered = d.buffered ++ ws := rfl
@[simp] theorem writeMany_root (d : Disk α) (ws : List (Nat × UInt8)) :
    (d.writeMany ws).root = d.root := rfl
@[simp] theorem writeMany_rootCached (d : Disk α) (ws : List (Nat × UInt8)) :
    (d.writeMany ws).rootCached = d.rootCached := rfl
@[simp] theorem writeMany_rootBuffered (d : Disk α) (ws : List (Nat × UInt8)) :
    (d.writeMany ws).rootBuffered = d.rootBuffered := rfl

@[simp] theorem writeMany_readRoot (d : Disk α) (ws : List (Nat × UInt8)) :
    (d.writeMany ws).readRoot = d.readRoot := rfl

/-- Overlaying writes that miss an address leaves it alone. -/
theorem overlay_of_not_mem {base : Nat → UInt8} : ∀ (ws : List (Nat × UInt8)) (a : Nat),
    (∀ v, (a, v) ∉ ws) → overlay base ws a = base a := by
  intro ws
  induction ws generalizing base with
  | nil => intro a _; rfl
  | cons w ws ih =>
      intro a h
      cases w with
      | mk x v =>
          rw [overlay, ih a (fun v' hv' => h v' (List.mem_cons_of_mem _ hv'))]
          have : a ≠ x := by
            intro hc; exact h v (by rw [hc]; exact List.mem_cons_self)
          simp [this]

/-! ### Laying an image down at an address -/

theorem mem_imgWrites : ∀ (bs : List UInt8) (b a : Nat) (v : UInt8),
    (a, v) ∈ imgWrites b bs → b ≤ a ∧ a < b + bs.length := by
  intro bs
  induction bs with
  | nil => intro b a v h; exact absurd h (by simp [imgWrites])
  | cons x xs ih =>
      intro b a v h
      rw [imgWrites] at h
      rcases List.mem_cons.mp h with h' | h'
      · have : a = b := congrArg (fun p => p.1) h'
        simp only [List.length_cons]; omega
      · have := ih (b + 1) a v h'
        simp only [List.length_cons]; omega

theorem overlay_imgWrites_get : ∀ (bs : List UInt8) (base : Nat → UInt8) (b i : Nat)
    (h : i < bs.length), overlay base (imgWrites b bs) (b + i) = bs[i]'h := by
  intro bs
  induction bs with
  | nil => intro base b i h; exact absurd h (by simp)
  | cons v vs ih =>
      intro base b i h
      cases i with
      | zero =>
          rw [imgWrites, show b + 0 = b by omega]
          show overlay (fun x => if x = b then v else base x) (imgWrites (b + 1) vs) b = _
          rw [overlay_of_not_mem _ b ?_]
          · simp
          · intro w hw
            have := mem_imgWrites _ _ _ _ hw
            omega
      | succ i =>
          have h' : i < vs.length := by simpa using h
          rw [imgWrites, show b + (i + 1) = b + 1 + i by omega]
          show overlay (fun x => if x = b then v else base x) (imgWrites (b + 1) vs) (b + 1 + i)
            = (v :: vs)[i + 1]
          rw [show ((v :: vs)[i + 1] : UInt8) = vs[i] from rfl]
          exact ih _ (b + 1) i h'

/-! ## Where each operation leaves things -/

@[simp] theorem flushUser_buffered (d : Disk α) : d.flushUser.buffered = [] := rfl
@[simp] theorem flushUser_rootBuffered (d : Disk α) : d.flushUser.rootBuffered = [] := rfl
@[simp] theorem flushUser_cached (d : Disk α) :
    d.flushUser.cached = d.cached ++ d.buffered := rfl
@[simp] theorem flushUser_rootCached (d : Disk α) :
    d.flushUser.rootCached = d.rootCached ++ d.rootBuffered := rfl

@[simp] theorem fsync_cached (d : Disk α) : d.fsync.cached = [] := rfl
@[simp] theorem fsync_rootCached (d : Disk α) : d.fsync.rootCached = [] := rfl
@[simp] theorem fsync_buffered (d : Disk α) : d.fsync.buffered = d.buffered := rfl
@[simp] theorem fsync_rootBuffered (d : Disk α) : d.fsync.rootBuffered = d.rootBuffered := rfl

@[simp] theorem sync_cached (d : Disk α) : d.sync.cached = [] := rfl
@[simp] theorem sync_buffered (d : Disk α) : d.sync.buffered = [] := rfl
@[simp] theorem sync_rootCached (d : Disk α) : d.sync.rootCached = [] := rfl
@[simp] theorem sync_rootBuffered (d : Disk α) : d.sync.rootBuffered = [] := rfl

@[simp] theorem writeRoot_buffered (d : Disk α) (r : α) :
    (d.writeRoot r).buffered = d.buffered := rfl
@[simp] theorem writeRoot_rootBuffered (d : Disk α) (r : α) :
    (d.writeRoot r).rootBuffered = d.rootBuffered ++ [r] := rfl

/-! ## What `sync` guarantees, and `flushUser` does not -/

@[simp] theorem sync_read (d : Disk α) (a : Nat) : d.sync.read a = d.read a := by
  rw [read_of_quiet (quiet_sync d)]
  show overlay (overlay d.stable (d.cached ++ d.buffered)) [] a = _
  rw [overlay_append]; rfl

@[simp] theorem sync_readRoot (d : Disk α) : d.sync.readRoot = d.readRoot := by
  rw [readRoot_of_quiet (quiet_sync d)]
  show ((d.rootCached ++ d.rootBuffered).getLast?).getD d.root = _
  rfl

@[simp] theorem sync_stable (d : Disk α) (a : Nat) : d.sync.stable a = d.read a := by
  rw [← sync_read d a, read_of_quiet (quiet_sync d)]

@[simp] theorem sync_root (d : Disk α) : d.sync.root = d.readRoot := by
  rw [← sync_readRoot d, readRoot_of_quiet (quiet_sync d)]

@[simp] theorem writeRoot_readRoot (d : Disk α) (r : α) : (d.writeRoot r).readRoot = r := by
  unfold Disk.writeRoot Disk.readRoot; simp

@[simp] theorem writeRoot_read (d : Disk α) (r : α) (a : Nat) : (d.writeRoot r).read a = d.read a :=
  rfl
@[simp] theorem writeRoot_stable (d : Disk α) (r : α) : (d.writeRoot r).stable = d.stable := rfl
@[simp] theorem writeRoot_cached (d : Disk α) (r : α) : (d.writeRoot r).cached = d.cached := rfl
@[simp] theorem writeRoot_rootCached (d : Disk α) (r : α) :
    (d.writeRoot r).rootCached = d.rootCached := rfl
@[simp] theorem writeRoot_root_eq (d : Disk α) (r : α) : (d.writeRoot r).root = d.root := rfl
@[simp] theorem writeRoot_stable_eq (d : Disk α) (r : α) (a : Nat) :
    (d.writeRoot r).stable a = d.stable a := rfl
@[simp] theorem flushUser_root (d : Disk α) : d.flushUser.root = d.root := rfl
@[simp] theorem flushUser_stable (d : Disk α) : d.flushUser.stable = d.stable := rfl

/-- A crash leaves untouched any address the kernel was never told about. -/
theorem crash_stable_of_no_cached {d d' : Disk α} (h : Crash d d') {a : Nat}
    (hp : ∀ v, (a, v) ∉ d.cached) : d'.stable a = d.stable a := by
  rcases h.1 a with hb | hb
  · exact hb
  · exact absurd hb (hp _)

/-- Regions agree when their bytes do. -/
theorem readRegion_congr {d₁ d₂ : Disk α} {base size : Nat}
    (h : ∀ i, i < size → d₁.read (base + i) = d₂.read (base + i)) :
    d₁.readRegion base size = d₂.readRegion base size := by
  unfold Disk.readRegion
  refine List.ext_getElem (by simp) ?_
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  exact h i (by simpa using h2)


end RaftKV.Disk
