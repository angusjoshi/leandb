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

/-- Write one byte into this process's buffer. -/
def Disk.write1 (d : Disk α) (a : Nat) (v : UInt8) : Disk α :=
  { d with buffered := d.buffered ++ [(a, v)] }

/-- Write a run of bytes starting at `a`. Individual bytes may land independently. -/
def Disk.writeBytes : Disk α → Nat → List UInt8 → Disk α
  | d, _, [] => d
  | d, a, v :: vs => (d.write1 a v).writeBytes (a + 1) vs

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

@[simp] theorem write1_read_self (d : Disk α) (a : Nat) (v : UInt8) :
    (d.write1 a v).read a = v := by
  unfold Disk.read Disk.write1
  dsimp only
  rw [overlay_snoc]
  simp

theorem write1_read_ne (d : Disk α) {x a : Nat} (v : UInt8) (h : x ≠ a) :
    (d.write1 a v).read x = d.read x := by
  unfold Disk.read Disk.write1
  dsimp only
  rw [overlay_snoc]
  simp [h]

@[simp] theorem write1_root (d : Disk α) (a : Nat) (v : UInt8) :
    (d.write1 a v).root = d.root := rfl
@[simp] theorem write1_stable (d : Disk α) (a : Nat) (v : UInt8) :
    (d.write1 a v).stable = d.stable := rfl
@[simp] theorem write1_cached (d : Disk α) (a : Nat) (v : UInt8) :
    (d.write1 a v).cached = d.cached := rfl
@[simp] theorem write1_rootCached (d : Disk α) (a : Nat) (v : UInt8) :
    (d.write1 a v).rootCached = d.rootCached := rfl

/-- A write outside a run leaves it alone. -/
theorem writeBytes_read_of_lt : ∀ (bs : List UInt8) (d : Disk α) (base x : Nat),
    x < base → (d.writeBytes base bs).read x = d.read x := by
  intro bs
  induction bs with
  | nil => intro d base x _; rfl
  | cons v vs ih =>
      intro d base x h
      rw [Disk.writeBytes, ih _ _ _ (by omega), write1_read_ne _ _ (by omega)]

theorem writeBytes_read_of_ge : ∀ (bs : List UInt8) (d : Disk α) (base x : Nat),
    base + bs.length ≤ x → (d.writeBytes base bs).read x = d.read x := by
  intro bs
  induction bs with
  | nil => intro d base x _; rfl
  | cons v vs ih =>
      intro d base x h
      simp only [List.length_cons] at h
      rw [Disk.writeBytes, ih _ _ _ (by omega), write1_read_ne _ _ (by omega)]

/-- Inside the run, a read gives back exactly what was written. -/
theorem writeBytes_read_get : ∀ (bs : List UInt8) (d : Disk α) (base i : Nat) (h : i < bs.length),
    (d.writeBytes base bs).read (base + i) = bs[i] := by
  intro bs
  induction bs with
  | nil => intro _ _ _ h; exact absurd h (by simp)
  | cons v vs ih =>
      intro d base i h
      cases i with
      | zero =>
          rw [Disk.writeBytes, writeBytes_read_of_lt _ _ _ _ (by omega)]
          simpa using write1_read_self d base v
      | succ i =>
          have h' : i < vs.length := by simpa using h
          have := ih (d.write1 base v) (base + 1) i h'
          rw [Disk.writeBytes, show base + (i + 1) = base + 1 + i by omega]
          simpa using this

@[simp] theorem writeBytes_stable : ∀ (bs : List UInt8) (d : Disk α) (base : Nat),
    (d.writeBytes base bs).stable = d.stable := by
  intro bs; induction bs with
  | nil => intro d base; rfl
  | cons v vs ih => intro d base; rw [Disk.writeBytes, ih]; rfl

@[simp] theorem writeBytes_cached : ∀ (bs : List UInt8) (d : Disk α) (base : Nat),
    (d.writeBytes base bs).cached = d.cached := by
  intro bs; induction bs with
  | nil => intro d base; rfl
  | cons v vs ih => intro d base; rw [Disk.writeBytes, ih]; rfl

@[simp] theorem writeBytes_root : ∀ (bs : List UInt8) (d : Disk α) (base : Nat),
    (d.writeBytes base bs).root = d.root := by
  intro bs; induction bs with
  | nil => intro d base; rfl
  | cons v vs ih => intro d base; rw [Disk.writeBytes, ih]; rfl

@[simp] theorem writeBytes_rootCached : ∀ (bs : List UInt8) (d : Disk α) (base : Nat),
    (d.writeBytes base bs).rootCached = d.rootCached := by
  intro bs; induction bs with
  | nil => intro d base; rfl
  | cons v vs ih => intro d base; rw [Disk.writeBytes, ih]; rfl

/-- Everything a run of writes leaves in flight lies inside the run. -/
theorem mem_writeBytes_buffered : ∀ (bs : List UInt8) (d : Disk α) (base a : Nat) (v : UInt8),
    (a, v) ∈ (d.writeBytes base bs).buffered →
    (a, v) ∈ d.buffered ∨ (base ≤ a ∧ a < base + bs.length) := by
  intro bs
  induction bs with
  | nil => intro d base a v h; exact Or.inl h
  | cons x xs ih =>
      intro d base a v h
      rw [Disk.writeBytes] at h
      rcases ih (d.write1 base x) (base + 1) a v h with h' | h'
      · rcases List.mem_append.mp h' with h'' | h''
        · exact Or.inl h''
        · right
          have := List.mem_singleton.mp h''
          have ha : a = base := congrArg (fun p => p.1) this
          simp only [List.length_cons]
          omega
      · right; simp only [List.length_cons]; omega

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
@[simp] theorem writeBytes_rootBuffered : ∀ (bs : List UInt8) (d : Disk α) (base : Nat),
    (d.writeBytes base bs).rootBuffered = d.rootBuffered := by
  intro bs; induction bs with
  | nil => intro d base; rfl
  | cons v vs ih => intro d base; rw [Disk.writeBytes, ih]; rfl
@[simp] theorem flushUser_root (d : Disk α) : d.flushUser.root = d.root := rfl
@[simp] theorem writeBytes_readRoot (bs : List UInt8) (d : Disk α) (base : Nat) :
    (d.writeBytes base bs).readRoot = d.readRoot := by
  unfold Disk.readRoot
  rw [writeBytes_rootCached, writeBytes_rootBuffered, writeBytes_root]
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

/-- A synced run of writes reads back exactly. -/
theorem readRegion_writeBytes_sync (d : Disk α) (base : Nat) (bs : List UInt8) :
    ((d.writeBytes base bs).sync).readRegion base bs.length = bs := by
  unfold Disk.readRegion
  refine List.ext_getElem (by simp) ?_
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [sync_read]
  exact writeBytes_read_get bs d base i (by simpa using h2)

end RaftKV.Disk
