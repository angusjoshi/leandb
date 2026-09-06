/-!
# A disk with realistic crash semantics

The storage proofs rest on a model of the device, and the model has to be
adversarial enough to be honest. Two facts about real storage matter:

* **A write may tear.** Bytes of a single write can land independently, so a
  crash can reveal a half-written image.
* **A write becomes durable at an unknown time.** After `write` returns, the
  data may reach the platter at any point up to the next `flush`, which forces
  it.

Both are captured by keeping, alongside the durable bytes, the writes issued
since the last flush; a crash then reveals, **independently at each address**,
either the old durable byte or *any* value written to that address since. That
is at least as adversarial as any real device: it permits tearing at byte
granularity and permits writes to a single address to land out of order.

## The one assumption

Nothing can be built on a device where *every* write tears — the commit point
would never be well defined. Real hardware provides a single aligned
sector-sized write that lands entirely or not at all, and this model provides
exactly one such thing: the **root cell**. Everything else is bytes and may
tear. That the device really offers this is the one storage assumption in the
trusted base, and it is stated here rather than buried in an implementation.

## Why the root cell is a type parameter

The commit discipline proved below — *write where the current root cannot see;
flush; swap the root atomically; flush* — is copy-on-write in miniature. With
`α := Bool` it is a two-region superblock, which is what this development uses.
With `α := PageId` it is an LMDB-style copy-on-write B-tree, where the root cell
holds the root page number and `alloc` returns a free page. The theorem is the
same one; only the instance changes.
-/

namespace RaftKV.Disk

/-!
Addresses are plain `Nat` rather than a named alias: `omega` cannot see through
an `abbrev`, and the layout arithmetic below leans on it heavily.
-/

/--
The device.

`bytes` and `root` are what a crash would reveal if nothing pending landed;
`pendingB` and `pendingR` are what has been written since the last flush,
oldest first.
-/
structure Disk (α : Type) where
  /-- Durable bytes. -/
  bytes : Nat → UInt8
  /-- Byte writes issued since the last flush, oldest first. -/
  pendingB : List (Nat × UInt8)
  /-- The durable root cell. -/
  root : α
  /-- Root writes issued since the last flush, oldest first. -/
  pendingR : List α

variable {α : Type}

/-- Overlay a list of byte writes on a base image; later writes win. -/
def overlay (base : Nat → UInt8) : List (Nat × UInt8) → (Nat → UInt8)
  | [] => base
  | (a, v) :: ws => overlay (fun x => if x = a then v else base x) ws

/-- What a read sees: the durable byte, as overwritten by anything pending. -/
def Disk.read (d : Disk α) (a : Nat) : UInt8 := overlay d.bytes d.pendingB a

/-- What a read of the root sees. -/
def Disk.readRoot (d : Disk α) : α := (d.pendingR.getLast?).getD d.root

/-- Write one byte. It may or may not be durable until a `flush`. -/
def Disk.write1 (d : Disk α) (a : Nat) (v : UInt8) : Disk α :=
  { d with pendingB := d.pendingB ++ [(a, v)] }

/-- Write a run of bytes starting at `a`. Individual bytes may land independently. -/
def Disk.writeBytes : Disk α → Nat → List UInt8 → Disk α
  | d, _, [] => d
  | d, a, v :: vs => (d.write1 a v).writeBytes (a + 1) vs

/-- Write the root cell. This is the one write that cannot tear. -/
def Disk.writeRoot (d : Disk α) (r : α) : Disk α :=
  { d with pendingR := d.pendingR ++ [r] }

/-- Force everything issued so far to be durable. -/
def Disk.flush (d : Disk α) : Disk α :=
  { bytes := d.read, pendingB := [], root := d.readRoot, pendingR := [] }

/-- Read `size` bytes from `base`. -/
def Disk.readRegion (d : Disk α) (base size : Nat) : List UInt8 :=
  (List.range size).map (fun i => d.read (base + i))

/--
**What a crash may reveal.**

Independently at each address, either the durable byte or any value written to
that address since the last flush; and for the root, either the durable value or
any value written to it since — never a mixture, which is the atomicity
assumption. Everything pending is then gone.
-/
def Crash (d d' : Disk α) : Prop :=
  (∀ a, d'.bytes a = d.bytes a ∨ (a, d'.bytes a) ∈ d.pendingB)
    ∧ (d'.root = d.root ∨ d'.root ∈ d.pendingR)
    ∧ d'.pendingB = [] ∧ d'.pendingR = []

/-- A disk with nothing outstanding: exactly what a `flush` leaves behind. -/
def Quiet (d : Disk α) : Prop := d.pendingB = [] ∧ d.pendingR = []

theorem quiet_flush (d : Disk α) : Quiet d.flush := ⟨rfl, rfl⟩

theorem crash_quiet {d d' : Disk α} (h : Crash d d') : Quiet d' := ⟨h.2.2.1, h.2.2.2⟩

/-- On a quiet disk, reads are the durable bytes. -/
theorem read_of_quiet {d : Disk α} (h : Quiet d) (a : Nat) : d.read a = d.bytes a := by
  unfold Disk.read; rw [h.1]; rfl

theorem readRoot_of_quiet {d : Disk α} (h : Quiet d) : d.readRoot = d.root := by
  unfold Disk.readRoot; rw [h.2]; rfl

/-- **A crash cannot disturb a quiet disk.** -/
theorem crash_of_quiet {d d' : Disk α} (hq : Quiet d) (h : Crash d d') :
    (∀ a, d'.bytes a = d.bytes a) ∧ d'.root = d.root := by
  refine ⟨fun a => ?_, ?_⟩
  · rcases h.1 a with hb | hb
    · exact hb
    · rw [hq.1] at hb; exact absurd hb (by simp)
  · rcases h.2.1 with hr | hr
    · exact hr
    · rw [hq.2] at hr; exact absurd hr (by simp)


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

@[simp] theorem write1_pendingR (d : Disk α) (a : Nat) (v : UInt8) :
    (d.write1 a v).pendingR = d.pendingR := rfl

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

/-- Everything a run of writes leaves pending lies inside the run. -/
theorem mem_writeBytes_pendingB : ∀ (bs : List UInt8) (d : Disk α) (base a : Nat) (v : UInt8),
    (a, v) ∈ (d.writeBytes base bs).pendingB →
    (a, v) ∈ d.pendingB ∨ (base ≤ a ∧ a < base + bs.length) := by
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

@[simp] theorem writeBytes_bytes : ∀ (bs : List UInt8) (d : Disk α) (base : Nat),
    (d.writeBytes base bs).bytes = d.bytes := by
  intro bs; induction bs with
  | nil => intro d base; rfl
  | cons v vs ih => intro d base; rw [Disk.writeBytes, ih]; rfl

/-- A crash leaves untouched any address with nothing pending. -/
theorem crash_bytes_of_no_pending {d d' : Disk α} (h : Crash d d') {a : Nat}
    (hp : ∀ v, (a, v) ∉ d.pendingB) : d'.bytes a = d.bytes a := by
  rcases h.1 a with hb | hb
  · exact hb
  · exact absurd hb (hp _)

@[simp] theorem writeBytes_root : ∀ (bs : List UInt8) (d : Disk α) (base : Nat),
    (d.writeBytes base bs).root = d.root := by
  intro bs; induction bs with
  | nil => intro d base; rfl
  | cons v vs ih => intro d base; rw [Disk.writeBytes, ih]; rfl

@[simp] theorem writeBytes_pendingR : ∀ (bs : List UInt8) (d : Disk α) (base : Nat),
    (d.writeBytes base bs).pendingR = d.pendingR := by
  intro bs; induction bs with
  | nil => intro d base; rfl
  | cons v vs ih => intro d base; rw [Disk.writeBytes, ih]; rfl

/-- A flushed run of writes reads back exactly. -/
theorem readRegion_writeBytes_flush (d : Disk α) (base : Nat) (bs : List UInt8) :
    ((d.writeBytes base bs).flush).readRegion base bs.length = bs := by
  unfold Disk.readRegion
  refine List.ext_getElem (by simp) ?_
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [read_of_quiet (quiet_flush _)]
  show (d.writeBytes base bs).read (base + i) = _
  rw [writeBytes_read_get bs d base i (by simpa using h2)]

@[simp] theorem flush_readRoot (d : Disk α) : d.flush.root = d.readRoot := rfl

@[simp] theorem writeRoot_readRoot (d : Disk α) (r : α) : (d.writeRoot r).readRoot = r := by
  unfold Disk.writeRoot Disk.readRoot; simp

@[simp] theorem writeRoot_read (d : Disk α) (r : α) (a : Nat) : (d.writeRoot r).read a = d.read a :=
  rfl

@[simp] theorem writeRoot_bytes (d : Disk α) (r : α) : (d.writeRoot r).bytes = d.bytes := rfl

@[simp] theorem writeRoot_pendingB (d : Disk α) (r : α) :
    (d.writeRoot r).pendingB = d.pendingB := rfl

@[simp] theorem writeRoot_pendingR (d : Disk α) (r : α) :
    (d.writeRoot r).pendingR = d.pendingR ++ [r] := rfl

@[simp] theorem flush_pendingR (d : Disk α) : d.flush.pendingR = [] := rfl

@[simp] theorem flush_pendingB (d : Disk α) : d.flush.pendingB = [] := rfl

@[simp] theorem flush_bytes (d : Disk α) : d.flush.bytes = d.read := rfl

@[simp] theorem flush_read (d : Disk α) (a : Nat) : d.flush.read a = d.read a := by
  rw [read_of_quiet (quiet_flush d)]; rfl

@[simp] theorem flush_readRoot' (d : Disk α) : d.flush.readRoot = d.readRoot := by
  rw [readRoot_of_quiet (quiet_flush d)]; rfl

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
