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
  /-- Force everything issued so far to be durable. -/
  | sync

/-- Run one operation. -/
def Op.run (d : Disk α) : Op α → Disk α
  | .writeAt base bs => d.writeBytes base bs
  | .setRoot r => d.writeRoot r
  | .sync => d.flush

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

/-- The operations of one commit. -/
def Format.commitOps (F : Format α V) (r : α) (v : V) : List (Op α) :=
  [.writeAt (F.regionOf (F.alloc r v)) (F.enc v), .sync, .setRoot (F.alloc r v), .sync]


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
  have hnop : ∀ i, i < F.lenOf d.readRoot → ∀ w,
      (F.regionOf d.readRoot + i, w) ∉
        (d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).pendingB := by
    intro i hi w hmem
    rcases mem_writeBytes_pendingB _ _ _ _ _ hmem with hm | hm
    · rw [hq.1] at hm; exact absurd hm (by simp)
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
          = ((d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).flush).read
              (F.regionOf (F.alloc d.readRoot v) + i)) →
      F.Holds e v := by
    intro e hqe hre hbe
    refine ⟨hqe, ?_⟩
    rw [hre, hlen]
    refine Eq.trans ?_ (readRegion_writeBytes_flush d (F.regionOf (F.alloc d.readRoot v)) (F.enc v))
    exact readRegion_congr hbe
  -- the four intermediate device states
  have h0 : runOps d ((F.commitOps d.readRoot v).take 0) = d := rfl
  have h1 : runOps d ((F.commitOps d.readRoot v).take 1)
      = d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v) := rfl
  have h2 : runOps d ((F.commitOps d.readRoot v).take 2)
      = (d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).flush := rfl
  have h3 : runOps d ((F.commitOps d.readRoot v).take 3)
      = ((d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).flush).writeRoot
          (F.alloc d.readRoot v) := rfl
  have h4 : ∀ n : Nat, runOps d ((F.commitOps d.readRoot v).take (n + 4))
      = (((d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).flush).writeRoot
          (F.alloc d.readRoot v)).flush := by
    intro n
    have hfull : (F.commitOps d.readRoot v).take (n + 4) = F.commitOps d.readRoot v := by
      rw [Format.commitOps]; simp
    rw [hfull]; rfl
  rcases k with _ | _ | _ | _ | k
  · -- crash before anything was issued
    rw [h0] at hc
    left
    obtain ⟨hb, hr⟩ := crash_of_quiet hq hc
    refine mkOld d' (crash_quiet hc) ?_ ?_
    · rw [readRoot_of_quiet (crash_quiet hc), hr, hrt]
    · intro i _
      rw [read_of_quiet (crash_quiet hc), hb, read_of_quiet hq]
  · -- mid-image: the live region has nothing pending, so it cannot have moved
    rw [h1] at hc
    left
    refine mkOld d' (crash_quiet hc) ?_ ?_
    · rw [readRoot_of_quiet (crash_quiet hc)]
      rcases hc.2.1 with hr | hr
      · rw [hr, writeBytes_root, hrt]
      · exfalso; rw [writeBytes_pendingR, hq.2] at hr; simp at hr
    · intro i hi
      rw [read_of_quiet (crash_quiet hc),
        crash_bytes_of_no_pending hc (hnop i hi), writeBytes_bytes, read_of_quiet hq]
  · -- after the image is durable, before the root moves
    rw [h2] at hc
    left
    obtain ⟨hb, hr⟩ := crash_of_quiet (quiet_flush _) hc
    refine mkOld d' (crash_quiet hc) ?_ ?_
    · rw [readRoot_of_quiet (crash_quiet hc), hr, flush_readRoot]
      unfold Disk.readRoot
      rw [writeBytes_pendingR, hq.2, writeBytes_root]
    · intro i hi
      rw [read_of_quiet (crash_quiet hc), hb, flush_bytes]
      exact hout i hi
  · -- during the root swap: atomic, so the old root or the new one
    rw [h3] at hc
    have hbyte : ∀ a, d'.bytes a
        = ((d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).flush).bytes a := by
      intro a
      exact crash_bytes_of_no_pending hc (by simp)
    rcases hc.2.1 with hr | hr
    · left
      refine mkOld d' (crash_quiet hc) ?_ ?_
      · rw [readRoot_of_quiet (crash_quiet hc), hr]
        show ((d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).flush).root = _
        rw [flush_readRoot]
        unfold Disk.readRoot
        rw [writeBytes_pendingR, hq.2, writeBytes_root]
      · intro i hi
        rw [read_of_quiet (crash_quiet hc), hbyte, flush_bytes]
        exact hout i hi
    · right
      refine mkNew d' (crash_quiet hc) ?_ ?_
      · rw [readRoot_of_quiet (crash_quiet hc)]
        simpa using hr
      · intro i _
        rw [read_of_quiet (crash_quiet hc), hbyte, flush_bytes, flush_read]
  · -- the commit completed
    rw [h4 k] at hc
    right
    obtain ⟨hb, hr⟩ := crash_of_quiet (quiet_flush _) hc
    refine mkNew d' (crash_quiet hc) ?_ ?_
    · rw [readRoot_of_quiet (crash_quiet hc), hr, flush_readRoot, writeRoot_readRoot]
    · intro i _
      rw [read_of_quiet (crash_quiet hc), hb, flush_bytes, writeRoot_read, flush_read]

/-- **A commit that completes leaves the new value in place.** -/
theorem Format.commit_holds (F : Format α V) {d : Disk α} {v₀ v : V} (h : F.Holds d v₀) :
    F.Holds (runOps d (F.commitOps d.readRoot v)) v := by
  have hlen : F.lenOf (F.alloc d.readRoot v) = (F.enc v).length := F.enc_len d.readRoot v
  have hrun : runOps d (F.commitOps d.readRoot v)
      = (((d.writeBytes (F.regionOf (F.alloc d.readRoot v)) (F.enc v)).flush).writeRoot
          (F.alloc d.readRoot v)).flush := rfl
  rw [hrun]
  refine ⟨quiet_flush _, ?_⟩
  rw [flush_readRoot', writeRoot_readRoot, hlen]
  refine Eq.trans ?_ (readRegion_writeBytes_flush d (F.regionOf (F.alloc d.readRoot v)) (F.enc v))
  refine readRegion_congr (fun i _ => ?_)
  rw [flush_read, writeRoot_read]

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

end RaftKV.Disk
