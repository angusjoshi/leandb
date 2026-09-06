import RaftKV.Storage.Disk

/-!
# Crash-safe commit, by copy-on-write

The one discipline that makes a store crash-safe on the device modelled in
`RaftKV.Storage.Disk`:

> **write where the live root cannot see it; flush; swap the root; flush.**

Nothing reachable from the current root is ever overwritten, so a torn write can
only damage space that no reader will look at. The root swap is the single
atomic action the device provides, and it is the commit point.

The result is `Format.commit_crash_safe`: crash at *any* point of a commit — in
the middle of the image write, between the two flushes, during the root swap —
and the store still holds either the old value or the new one, in a state ready
for the next commit. Never a mixture, never garbage.

This is stated over an abstract root, so the same theorem covers both instances
we care about. With the root a `Bool` it is the two-region superblock this
development uses. With the root a page number and `alloc` returning a free page
it is an LMDB-style copy-on-write B-tree, which is where log compaction wants to
go — the commit argument does not change, only `regionOf` and `alloc`.
-/

namespace RaftKV.Disk

variable {α V : Type}

/-- One device operation. -/
inductive Op (α : Type) where
  /-- Write an image, byte by byte; it may tear. -/
  | writeAt (base : Nat) (bs : List UInt8)
  /-- Swap the root. Atomic. -/
  | setRoot (r : α)
  /-- Hand this process's buffer to the kernel. **Not** durability. -/
  | flushUser
  /-- Force what the kernel holds onto the platter. This is the durable one. -/
  | fsync

/-- Run one operation. -/
def Op.run (d : Disk α) : Op α → Disk α
  | .writeAt base bs => d.writeBytes base bs
  | .setRoot r => d.writeRoot r
  | .flushUser => d.flushUser
  | .fsync => d.fsync

/-- Run a sequence of operations. -/
def runOps (d : Disk α) : List (Op α) → Disk α
  | [] => d
  | o :: os => runOps (o.run d) os

/--
An on-device format: where the root points, how to find the next place to write,
and how values are encoded.
-/
structure Format (α V : Type) where
  /-- Where the image a root points at begins. -/
  regionOf : α → Nat
  /-- How long that image is. Carrying the length in the root is what lets
  images vary in size — a growing log cannot live in a fixed region. -/
  lenOf : α → Nat
  /-- The root to commit next, for this value. -/
  alloc : α → V → α
  /-- Serialise. -/
  enc : V → List UInt8
  /-- Deserialise. -/
  dec : List UInt8 → Option V
  /-- The next root describes the image about to be written. -/
  enc_len : ∀ r v, lenOf (alloc r v) = (enc v).length
  /-- Round-trip. -/
  dec_enc : ∀ v, dec (enc v) = some v
  /-- **Copy-on-write**: the image being written never overlaps the live one. -/
  disjoint : ∀ r v, regionOf (alloc r v) + lenOf (alloc r v) ≤ regionOf r
    ∨ regionOf r + lenOf r ≤ regionOf (alloc r v)

/-- Read back whatever the root currently points at. -/
def Format.recover (F : Format α V) (d : Disk α) : Option V :=
  F.dec (d.readRegion (F.regionOf d.readRoot) (F.lenOf d.readRoot))

/-- The device is quiet and its live region holds `v`. -/
def Format.Holds (F : Format α V) (d : Disk α) (v : V) : Prop :=
  Quiet d ∧ d.readRegion (F.regionOf d.readRoot) (F.lenOf d.readRoot) = F.enc v

/-- What `Holds` was for: recovery returns the value. -/
theorem Format.recover_of_holds (F : Format α V) {d : Disk α} {v : V} (h : F.Holds d v) :
    F.recover d = some v := by
  unfold Format.recover; rw [h.2]; exact F.dec_enc v

/--
The operations of one commit.

Both `fsync`s are load-bearing. The first makes the image durable *before* the
root can point at it; the second makes the root swap itself durable. Dropping
either leaves the corresponding bytes in the kernel, where the crash relation is
free to lose them — see `flushOnly_not_crash_safe`.
-/
def Format.commitOps (F : Format α V) (r : α) (v : V) : List (Op α) :=
  [.writeAt (F.regionOf (F.alloc r v)) (F.enc v), .flushUser, .fsync,
   .setRoot (F.alloc r v), .flushUser, .fsync]

/-!
## The theorem

A crash at any point of a commit leaves the store holding the old value or the
new one, and ready for the next commit.
-/

theorem Format.commit_crash_safe (F : Format α V) {d : Disk α} {v₀ v : V}
    (h : F.Holds d v₀) (k : Nat) {d' : Disk α}
    (hc : Crash (runOps d ((F.commitOps d.readRoot v).take k)) d') :
    F.Holds d' v₀ ∨ F.Holds d' v := by
  obtain ⟨hq, hreg⟩ := h
  have hlen : F.lenOf (F.alloc d.readRoot v) = (F.enc v).length := F.enc_len d.readRoot v
  have hdis := F.disjoint d.readRoot v
  have hrt : d.readRoot = d.root := readRoot_of_quiet hq
  -- the image is written where the live root cannot see it
  have hout : ∀ i, i < F.lenOf d.readRoot →
      (d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).read
          (F.regionOf d.readRoot + i)
        = d.read (F.regionOf d.readRoot + i) := by
    intro i hi
    rcases hdis with hd | hd
    · exact writeBytes_read_of_ge _ _ _ _ (by omega)
    · exact writeBytes_read_of_lt _ _ _ _ (by omega)
  -- nothing the kernel holds touches the live region, at any point of the commit
  have hnop : ∀ i, i < F.lenOf d.readRoot → ∀ w,
      (F.regionOf d.readRoot + i, w) ∉
        ((d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).flushUser).cached := by
    intro i hi w hmem
    have hmem' : (F.regionOf d.readRoot + i, w) ∈
        (d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).cached
          ++ (d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).buffered := hmem
    rcases List.mem_append.mp hmem' with hm | hm
    · rw [writeBytes_cached, hq.1] at hm; exact absurd hm (by simp)
    · rcases mem_writeBytes_buffered _ _ _ _ _ hm with hm' | hm'
      · rw [hq.2.1] at hm'; exact absurd hm' (by simp)
      · rcases hdis with hd | hd <;> omega
  -- the two ways to conclude
  have mkOld : ∀ e : Disk α, Quiet e → e.readRoot = d.readRoot →
      (∀ i, i < F.lenOf d.readRoot →
        e.read (F.regionOf d.readRoot + i) = d.read (F.regionOf d.readRoot + i)) →
      F.Holds e v₀ := by
    intro e hqe hre hbe
    refine ⟨hqe, ?_⟩
    rw [hre, ← hreg]
    exact readRegion_congr hbe
  have mkNew : ∀ e : Disk α, Quiet e → e.readRoot = F.alloc d.readRoot v →
      (∀ i, i < (F.enc v).length →
        e.read (F.regionOf (F.alloc d.readRoot v) + i)
          = ((d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).sync).read
              (F.regionOf (F.alloc d.readRoot v) + i)) →
      F.Holds e v := by
    intro e hqe hre hbe
    refine ⟨hqe, ?_⟩
    rw [hre, hlen]
    refine Eq.trans ?_ (readRegion_writeBytes_sync d (F.regionOf (F.alloc d.readRoot v)) (F.enc v))
    exact readRegion_congr hbe
  -- the six intermediate device states
  have h0 : runOps d ((F.commitOps d.readRoot v).take 0) = d := rfl
  have h1 : runOps d ((F.commitOps d.readRoot v).take 1)
      = d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v) := rfl
  have h2 : runOps d ((F.commitOps d.readRoot v).take 2)
      = (d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).flushUser := rfl
  have h3 : runOps d ((F.commitOps d.readRoot v).take 3)
      = (d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).sync := rfl
  have h4 : runOps d ((F.commitOps d.readRoot v).take 4)
      = ((d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).sync).writeRoot
          (F.alloc d.readRoot v) := rfl
  have h5 : runOps d ((F.commitOps d.readRoot v).take 5)
      = (((d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).sync).writeRoot
          (F.alloc d.readRoot v)).flushUser := rfl
  have h6 : ∀ n : Nat, runOps d ((F.commitOps d.readRoot v).take (n + 6))
      = (((d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).sync).writeRoot
          (F.alloc d.readRoot v)).sync := by
    intro n
    have hfull : (F.commitOps d.readRoot v).take (n + 6) = F.commitOps d.readRoot v := by
      rw [Format.commitOps]; simp
    rw [hfull]; rfl
  -- after the first sync the image is durable and the root has not moved
  have hsyncRoot : ((d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).sync).root
      = d.root := by
    rw [sync_root, writeBytes_readRoot, hrt]
  rcases k with _ | _ | _ | _ | _ | _ | k
  · -- crash before anything was issued
    rw [h0] at hc
    left
    obtain ⟨hb, hr⟩ := crash_of_quiet hq hc
    refine mkOld d' (crash_quiet hc) ?_ ?_
    · rw [readRoot_of_quiet (crash_quiet hc), hr, hrt]
    · intro i _
      rw [read_of_quiet (crash_quiet hc), hb, read_of_quiet hq]
  · -- mid-image, still in this process's buffer: the kernel never saw any of it
    rw [h1] at hc
    left
    refine mkOld d' (crash_quiet hc) ?_ ?_
    · rw [readRoot_of_quiet (crash_quiet hc)]
      rcases hc.2.1 with hr | hr
      · rw [hr, writeBytes_root, hrt]
      · exfalso; simp [hq.2.2.1] at hr
    · intro i hi
      rw [read_of_quiet (crash_quiet hc),
        crash_stable_of_no_cached hc (by rw [writeBytes_cached, hq.1]; simp),
        writeBytes_stable, read_of_quiet hq]
  · -- flushed but not fsynced: the image is the kernel's, and may be lost —
    -- but it was written where the live root cannot see it, so who cares
    rw [h2] at hc
    left
    refine mkOld d' (crash_quiet hc) ?_ ?_
    · rw [readRoot_of_quiet (crash_quiet hc)]
      rcases hc.2.1 with hr | hr
      · rw [hr]
        show (d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).root = _
        rw [writeBytes_root, hrt]
      · exfalso
        have hr' : d'.root ∈
            (d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).rootCached
              ++ (d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).rootBuffered := hr
        rcases List.mem_append.mp hr' with hm | hm
        · simp [hq.2.2.1] at hm
        · simp [hq.2.2.2] at hm
    · intro i hi
      rw [read_of_quiet (crash_quiet hc), crash_stable_of_no_cached hc (hnop i hi)]
      show (d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).stable _ = _
      rw [writeBytes_stable, read_of_quiet hq]
  · -- the image is durable, the root has not moved
    rw [h3] at hc
    left
    obtain ⟨hb, hr⟩ := crash_of_quiet (quiet_sync _) hc
    refine mkOld d' (crash_quiet hc) ?_ ?_
    · rw [readRoot_of_quiet (crash_quiet hc), hr, hsyncRoot, hrt]
    · intro i hi
      rw [read_of_quiet (crash_quiet hc), hb, sync_stable]
      exact hout i hi
  · -- the root swap is in this process's buffer: a crash simply loses it
    rw [h4] at hc
    left
    refine mkOld d' (crash_quiet hc) ?_ ?_
    · rw [readRoot_of_quiet (crash_quiet hc)]
      rcases hc.2.1 with hr | hr
      · rw [hr, writeRoot_root_eq, hsyncRoot, hrt]
      · exfalso; simp at hr
    · intro i hi
      rw [read_of_quiet (crash_quiet hc),
        crash_stable_of_no_cached hc (by rw [writeRoot_cached]; simp), writeRoot_stable_eq,
        sync_stable]
      exact hout i hi
  · -- the root swap is the kernel's: atomic, so the old root or the new one
    rw [h5] at hc
    have hbyte : ∀ a, d'.stable a
        = ((d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).sync).stable a := by
      intro a
      refine crash_stable_of_no_cached hc ?_
      intro w hw
      have hw' : (a, w) ∈
          (((d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).sync).writeRoot
            (F.alloc d.readRoot v)).cached
            ++ (((d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).sync).writeRoot
              (F.alloc d.readRoot v)).buffered := hw
      rcases List.mem_append.mp hw' with hm | hm
      · simp at hm
      · simp at hm
    rcases hc.2.1 with hr | hr
    · left
      refine mkOld d' (crash_quiet hc) ?_ ?_
      · rw [readRoot_of_quiet (crash_quiet hc), hr]
        show (((d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).sync).writeRoot
          (F.alloc d.readRoot v)).flushUser.root = _
        rw [flushUser_root, writeRoot_root_eq, hsyncRoot, hrt]
      · intro i hi
        rw [read_of_quiet (crash_quiet hc), hbyte, sync_stable]
        exact hout i hi
    · right
      refine mkNew d' (crash_quiet hc) ?_ ?_
      · rw [readRoot_of_quiet (crash_quiet hc)]
        show d'.root = _
        have : (((d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).sync).writeRoot
            (F.alloc d.readRoot v)).flushUser.rootCached = [F.alloc d.readRoot v] := by
          show _ ++ _ = _
          simp
        rw [this] at hr
        simpa using hr
      · intro i _
        rw [read_of_quiet (crash_quiet hc), hbyte, sync_stable, sync_read]
  · -- the commit completed
    rw [h6 k] at hc
    right
    obtain ⟨hb, hr⟩ := crash_of_quiet (quiet_sync _) hc
    refine mkNew d' (crash_quiet hc) ?_ ?_
    · rw [readRoot_of_quiet (crash_quiet hc), hr, sync_root, writeRoot_readRoot]
    · intro i _
      rw [read_of_quiet (crash_quiet hc), hb, sync_stable, writeRoot_read, sync_read]

/-- **A commit that completes leaves the new value in place.** -/
theorem Format.commit_holds (F : Format α V) {d : Disk α} {v₀ v : V} (h : F.Holds d v₀) :
    F.Holds (runOps d (F.commitOps d.readRoot v)) v := by
  have hlen : F.lenOf (F.alloc d.readRoot v) = (F.enc v).length := F.enc_len d.readRoot v
  have hrun : runOps d (F.commitOps d.readRoot v)
      = (((d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).sync).writeRoot
          (F.alloc d.readRoot v)).sync := rfl
  rw [hrun]
  refine ⟨quiet_sync _, ?_⟩
  rw [sync_readRoot, writeRoot_readRoot, hlen]
  refine Eq.trans ?_ (readRegion_writeBytes_sync d (F.regionOf (F.alloc d.readRoot v)) (F.enc v))
  refine readRegion_congr (fun i _ => ?_)
  rw [sync_read, writeRoot_read]

/-- **Recovery after a crash returns the old value or the new one — never garbage.** -/
theorem Format.recover_crash (F : Format α V) {d : Disk α} {v₀ v : V}
    (h : F.Holds d v₀) (k : Nat) {d' : Disk α}
    (hc : Crash (runOps d ((F.commitOps d.readRoot v).take k)) d') :
    F.recover d' = some v₀ ∨ F.recover d' = some v :=
  (F.commit_crash_safe h k hc).imp F.recover_of_holds F.recover_of_holds

/-! ## The two-region instance

The simplest copy-on-write layout: two images side by side, the root cell saying
which one is live and how long it is. `alloc` flips the side, so a commit always
writes the region that is not being read.
-/

/-- Two images of at most `capacity` bytes, at `0` and at `capacity`. -/
def twoRegion (capacity : Nat) (enc : V → List UInt8) (dec : List UInt8 → Option V)
    (enc_le : ∀ v, (enc v).length ≤ capacity) (dec_enc : ∀ v, dec (enc v) = some v) :
    Format (Bool × Nat) V where
  regionOf := fun p => if p.1 then capacity else 0
  lenOf := fun p => min p.2 capacity
  alloc := fun p v => (!p.1, (enc v).length)
  enc := enc
  dec := dec
  enc_len := by intro r v; dsimp only; exact Nat.min_eq_left (enc_le v)
  dec_enc := dec_enc
  disjoint := by
    intro r v
    cases hr : r.1 <;> simp [hr] <;> omega


/-! ## The `fsync` is load-bearing

It would be easy to write a commit that only ever calls `flush` — Lean's
`IO.FS.Handle` offers nothing else — and to believe the proof above still
applies. It does not, and this is the counterexample that shows why.

Flushing moves bytes from this process to the kernel. The crash relation is then
free to lose them, independently at each address, which is exactly the freedom
`fsync` removes. So a flush-only commit can crash with the *root* landed and the
*image* not, leaving the root pointing at a region that was never written.
-/

/-- A commit that flushes but never fsyncs. -/
def Format.commitOpsFlushOnly (F : Format α V) (r : α) (v : V) : List (Op α) :=
  [.writeAt (F.regionOf (F.alloc r v)) (F.enc v), .flushUser,
   .setRoot (F.alloc r v), .flushUser]

/-- A one-byte format: `1` encodes `true`, `2` encodes `false`, `0` is not an encoding. -/
def tiny : Format (Bool × Nat) Bool :=
  twoRegion 1 (fun b => [if b then 1 else 2])
    (fun bs => match bs with
      | [x] => if x = 1 then some true else if x = 2 then some false else none
      | _ => none)
    (by intro v; cases v <;> exact Nat.le_refl _)
    (by intro v; cases v <;> rfl)

/-- A device holding `true` in region 0, with region 1 never written. -/
def tinyDisk (r : Bool × Nat) : Disk (Bool × Nat) where
  stable := fun a => if a = 0 then 1 else 0
  cached := []
  buffered := []
  root := r
  rootCached := []
  rootBuffered := []

/--
**A commit without `fsync` is not crash-safe.**

There is a device holding `true`, a flush-only commit of `false`, and a crash
after which recovery returns *neither* — the root swap reached the platter and
the image did not, so the root names a region that was never written.

This is why `Format.commitOps` calls `fsync` and not merely `flushUser`, and why
the disk model distinguishes the two. With a two-level model — durable and
not-yet-durable — the distinction is inexpressible and this failure is invisible.
-/
theorem flushOnly_not_crash_safe :
    ∃ (d d' : Disk (Bool × Nat)) (v₀ v : Bool),
      tiny.Holds d v₀
        ∧ Crash (runOps d (tiny.commitOpsFlushOnly d.readRoot v)) d'
        ∧ tiny.recover d' ≠ some v₀ ∧ tiny.recover d' ≠ some v := by
  refine ⟨tinyDisk (false, 1), tinyDisk (true, 1), true, false, ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩, ?_, ?_, ?_⟩
  · refine ⟨fun a => Or.inl rfl, Or.inr ?_, rfl, rfl, rfl, rfl⟩
    show (true, 1) ∈ ([] ++ [] : List (Bool × Nat)) ++ [(true, 1)]
    simp
  · decide
  · decide

end RaftKV.Disk
