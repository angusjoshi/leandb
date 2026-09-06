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
  /-- Write a set of bytes; they may tear. -/
  | write (ws : List (Nat × UInt8))
  /-- Swap the root. Atomic. -/
  | setRoot (r : α)
  /-- Hand this process's buffer to the kernel. **Not** durability. -/
  | flushUser
  /-- Force what the kernel holds onto the platter. This is the durable one. -/
  | fsync

/-- Run one operation. -/
def Op.run (d : Disk α) : Op α → Disk α
  | .write ws => d.writeMany ws
  | .setRoot r => d.writeRoot r
  | .flushUser => d.flushUser
  | .fsync => d.fsync

/-- Run a sequence of operations. -/
def runOps (d : Disk α) : List (Op α) → Disk α
  | [] => d
  | o :: os => runOps (o.run d) os

/--
An on-device format.

The value under a root is not required to live in one contiguous run: `reach`
says which addresses it occupies, and it may be a scattered set of pages. That
is what lets one theorem cover both a two-region superblock and a copy-on-write
B-tree.

Three laws, and they are exactly the three the crash-safety argument uses:

* `frame` — reading depends only on what the root can reach, so a write
  elsewhere is invisible;
* `fresh` — **copy-on-write**: a commit writes nothing the live root can reach;
* `correct` — after those writes, the new root reads back the new value.

Only `correct` is about the data structure being any good. `frame` and `fresh`
are about where bytes go, and they are what make a crash survivable.
-/
structure Format (α V : Type) where
  /-- The addresses the value under this root occupies. -/
  reach : α → Nat → Prop
  /-- Decode the value under this root from a byte image. -/
  readVal : (Nat → UInt8) → α → Option V
  /-- The root a commit of `v` over `r` installs. -/
  alloc : α → V → α
  /-- The bytes a commit of `v` over `r` writes. -/
  writes : α → V → List (Nat × UInt8)
  /-- Reading depends only on reachable addresses. -/
  frame : ∀ (f g : Nat → UInt8) (r : α), (∀ a, reach r a → f a = g a) → readVal f r = readVal g r
  /-- **Copy-on-write**: a commit never writes where the live root can see. -/
  fresh : ∀ (r : α) (v : V) (a : Nat) (w : UInt8), (a, w) ∈ writes r v → ¬ reach r a
  /-- After the commit's writes, the new root reads back the new value. -/
  correct : ∀ (f : Nat → UInt8) (r : α) (v : V),
    readVal (overlay f (writes r v)) (alloc r v) = some v

/-- Read back whatever the root currently points at. -/
def Format.recover (F : Format α V) (d : Disk α) : Option V :=
  F.readVal (fun a => d.read a) d.readRoot

/-- The device is quiet and its live root reads `v`. -/
def Format.Holds (F : Format α V) (d : Disk α) (v : V) : Prop :=
  Quiet d ∧ F.readVal d.stable d.readRoot = some v

/-- What `Holds` was for: recovery returns the value. -/
theorem Format.recover_of_holds (F : Format α V) {d : Disk α} {v : V} (h : F.Holds d v) :
    F.recover d = some v := by
  unfold Format.recover
  rw [F.frame _ d.stable d.readRoot (fun a _ => read_of_quiet h.1 a)]
  exact h.2

/--
The operations of one commit.

Both `fsync`s are load-bearing. The first makes the new bytes durable *before*
the root can point at them; the second makes the root swap itself durable.
Dropping either leaves the corresponding bytes in the kernel, where the crash
relation is free to lose them — see `flushOnly_not_crash_safe`.
-/
def Format.commitOps (F : Format α V) (r : α) (v : V) : List (Op α) :=
  [.write (F.writes r v), .flushUser, .fsync,
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
  have hrt : d.readRoot = d.root := readRoot_of_quiet hq
  -- the six intermediate device states
  have h0 : runOps d ((F.commitOps d.readRoot v).take 0) = d := rfl
  have h1 : runOps d ((F.commitOps d.readRoot v).take 1)
      = d.writeMany (F.writes d.readRoot v) := rfl
  have h2 : runOps d ((F.commitOps d.readRoot v).take 2)
      = (d.writeMany (F.writes d.readRoot v)).flushUser := rfl
  have h3 : runOps d ((F.commitOps d.readRoot v).take 3)
      = (d.writeMany (F.writes d.readRoot v)).sync := rfl
  have h4 : runOps d ((F.commitOps d.readRoot v).take 4)
      = ((d.writeMany (F.writes d.readRoot v)).sync).writeRoot (F.alloc d.readRoot v) := rfl
  have h5 : runOps d ((F.commitOps d.readRoot v).take 5)
      = (((d.writeMany (F.writes d.readRoot v)).sync).writeRoot
          (F.alloc d.readRoot v)).flushUser := rfl
  have h6 : ∀ n : Nat, runOps d ((F.commitOps d.readRoot v).take (n + 6))
      = (((d.writeMany (F.writes d.readRoot v)).sync).writeRoot (F.alloc d.readRoot v)).sync := by
    intro n
    have hfull : (F.commitOps d.readRoot v).take (n + 6) = F.commitOps d.readRoot v := by
      rw [Format.commitOps]; simp
    rw [hfull]; rfl
  -- after the first sync the new bytes are on the platter, and nowhere else moved
  have hsyncStable : ∀ a, ((d.writeMany (F.writes d.readRoot v)).sync).stable a
      = overlay d.stable (F.writes d.readRoot v) a := by
    intro a
    rw [sync_stable]
    show overlay (overlay d.stable d.cached) (d.buffered ++ F.writes d.readRoot v) a = _
    rw [hq.1, hq.2.1]
    rfl
  have hsyncRoot : ((d.writeMany (F.writes d.readRoot v)).sync).root = d.root := by
    rw [sync_root, writeMany_readRoot, hrt]
  -- the two ways to conclude
  have hold : ∀ e : Disk α, Quiet e → e.readRoot = d.readRoot →
      (∀ a, F.reach d.readRoot a → e.stable a = d.stable a) → F.Holds e v₀ := by
    intro e hqe hre hbe
    exact ⟨hqe, by rw [hre, F.frame e.stable d.stable d.readRoot hbe]; exact hreg⟩
  have hnew : ∀ e : Disk α, Quiet e → e.readRoot = F.alloc d.readRoot v →
      (∀ a, e.stable a = overlay d.stable (F.writes d.readRoot v) a) → F.Holds e v := by
    intro e hqe hre hbe
    refine ⟨hqe, ?_⟩
    rw [hre, F.frame e.stable (overlay d.stable (F.writes d.readRoot v)) _ (fun a _ => hbe a)]
    exact F.correct d.stable d.readRoot v
  -- copy-on-write: at any reachable address, the commit's writes are absent
  have hcow : ∀ a, F.reach d.readRoot a →
      overlay d.stable (F.writes d.readRoot v) a = d.stable a := by
    intro a ha
    exact overlay_of_not_mem _ a (fun w hw => absurd ha (F.fresh d.readRoot v a w hw))
  rcases k with _ | _ | _ | _ | _ | _ | k
  · -- crash before anything was issued
    rw [h0] at hc
    left
    obtain ⟨hb, hr⟩ := crash_of_quiet hq hc
    exact hold d' (crash_quiet hc) (by rw [readRoot_of_quiet (crash_quiet hc), hr, hrt])
      (fun a _ => hb a)
  · -- mid-write, still in this process's buffer: the kernel never saw any of it
    rw [h1] at hc
    left
    refine hold d' (crash_quiet hc) ?_ (fun a _ => ?_)
    · rw [readRoot_of_quiet (crash_quiet hc)]
      rcases hc.2.1 with hr | hr
      · rw [hr, writeMany_root, hrt]
      · exfalso; simp [hq.2.2.1] at hr
    · rw [crash_stable_of_no_cached hc (by simp [hq.1]), writeMany_stable]
  · -- flushed but not fsynced: the kernel may keep or lose any of it, and it does
    -- not matter, because copy-on-write put all of it out of the live root's sight
    rw [h2] at hc
    left
    refine hold d' (crash_quiet hc) ?_ (fun a ha => ?_)
    · rw [readRoot_of_quiet (crash_quiet hc)]
      rcases hc.2.1 with hr | hr
      · rw [hr]
        show (d.writeMany (F.writes d.readRoot v)).root = _
        rw [writeMany_root, hrt]
      · exfalso
        have hr' : d'.root ∈ d.rootCached ++ d.rootBuffered := hr
        rcases List.mem_append.mp hr' with hm | hm
        · rw [hq.2.2.1] at hm; exact absurd hm (by simp)
        · rw [hq.2.2.2] at hm; exact absurd hm (by simp)
    · rcases hc.1 a with hx | hx
      · rw [hx]; rfl
      · exfalso
        have hx' : (a, d'.stable a) ∈ d.cached ++ (d.buffered ++ F.writes d.readRoot v) := hx
        rcases List.mem_append.mp hx' with hm | hm
        · rw [hq.1] at hm; exact absurd hm (by simp)
        · rcases List.mem_append.mp hm with hm' | hm'
          · rw [hq.2.1] at hm'; exact absurd hm' (by simp)
          · exact absurd ha (F.fresh d.readRoot v a _ hm')
  · -- the new bytes are durable, the root has not moved
    rw [h3] at hc
    left
    obtain ⟨hb, hr⟩ := crash_of_quiet (quiet_sync _) hc
    refine hold d' (crash_quiet hc) (by rw [readRoot_of_quiet (crash_quiet hc), hr, hsyncRoot, hrt])
      (fun a ha => ?_)
    rw [hb a, hsyncStable a, hcow a ha]
  · -- the root swap is in this process's buffer: a crash simply loses it
    rw [h4] at hc
    left
    refine hold d' (crash_quiet hc) ?_ (fun a ha => ?_)
    · rw [readRoot_of_quiet (crash_quiet hc)]
      rcases hc.2.1 with hr | hr
      · rw [hr, writeRoot_root_eq, hsyncRoot, hrt]
      · exfalso; simp at hr
    · rw [crash_stable_of_no_cached hc (by simp), writeRoot_stable_eq, hsyncStable a, hcow a ha]
  · -- the root swap is the kernel's: atomic, so the old root or the new one
    rw [h5] at hc
    have hbyte : ∀ a, d'.stable a = overlay d.stable (F.writes d.readRoot v) a := by
      intro a
      rw [crash_stable_of_no_cached hc (by simp)]
      show ((d.writeMany (F.writes d.readRoot v)).sync).stable a = _
      exact hsyncStable a
    rcases hc.2.1 with hr | hr
    · left
      refine hold d' (crash_quiet hc) ?_ (fun a ha => ?_)
      · rw [readRoot_of_quiet (crash_quiet hc), hr]
        show (((d.writeMany (F.writes d.readRoot v)).sync).writeRoot
          (F.alloc d.readRoot v)).flushUser.root = _
        rw [flushUser_root, writeRoot_root_eq, hsyncRoot, hrt]
      · rw [hbyte a, hcow a ha]
    · right
      refine hnew d' (crash_quiet hc) ?_ hbyte
      rw [readRoot_of_quiet (crash_quiet hc)]
      have hrc : (((d.writeMany (F.writes d.readRoot v)).sync).writeRoot
          (F.alloc d.readRoot v)).flushUser.rootCached = [F.alloc d.readRoot v] := by
        show _ ++ _ = _; simp
      rw [hrc] at hr
      simpa using hr
  · -- the commit completed
    rw [h6 k] at hc
    right
    obtain ⟨hb, hr⟩ := crash_of_quiet (quiet_sync _) hc
    refine hnew d' (crash_quiet hc) ?_ (fun a => ?_)
    · rw [readRoot_of_quiet (crash_quiet hc), hr, sync_root, writeRoot_readRoot]
    · rw [hb a, sync_stable, writeRoot_read]
      show ((d.writeMany (F.writes d.readRoot v)).sync).read a = _
      rw [read_of_quiet (quiet_sync _)]
      exact hsyncStable a

/-- **A commit that completes leaves the new value in place.** -/
theorem Format.commit_holds (F : Format α V) {d : Disk α} {v₀ v : V} (h : F.Holds d v₀) :
    F.Holds (runOps d (F.commitOps d.readRoot v)) v := by
  obtain ⟨hq, _⟩ := h
  have hrun : runOps d (F.commitOps d.readRoot v)
      = (((d.writeMany (F.writes d.readRoot v)).sync).writeRoot (F.alloc d.readRoot v)).sync :=
    rfl
  rw [hrun]
  refine ⟨quiet_sync _, ?_⟩
  rw [sync_readRoot, writeRoot_readRoot]
  have hst : ∀ a, ((((d.writeMany (F.writes d.readRoot v)).sync).writeRoot
      (F.alloc d.readRoot v)).sync).stable a = overlay d.stable (F.writes d.readRoot v) a := by
    intro a
    rw [sync_stable, writeRoot_read]
    show ((d.writeMany (F.writes d.readRoot v)).sync).read a = _
    rw [read_of_quiet (quiet_sync _), sync_stable]
    show overlay (overlay d.stable d.cached) (d.buffered ++ F.writes d.readRoot v) a = _
    rw [hq.1, hq.2.1]; rfl
  rw [F.frame _ (overlay d.stable (F.writes d.readRoot v)) _ (fun a _ => hst a)]
  exact F.correct d.stable d.readRoot v

/-- **Recovery after a crash returns the old value or the new one — never garbage.** -/
theorem Format.recover_crash (F : Format α V) {d : Disk α} {v₀ v : V}
    (h : F.Holds d v₀) (k : Nat) {d' : Disk α}
    (hc : Crash (runOps d ((F.commitOps d.readRoot v).take k)) d') :
    F.recover d' = some v₀ ∨ F.recover d' = some v :=
  (F.commit_crash_safe h k hc).imp F.recover_of_holds F.recover_of_holds

/-! ## The two-region instance

The simplest copy-on-write layout: two images side by side, the root cell saying
which is live and how long it is. `alloc` flips the side, so a commit always
writes the region that is not being read.
-/

/-- Where the image for a root begins. -/
def tr.base (capacity : Nat) (p : Bool × Nat) : Nat := if p.1 then capacity else 0

/-- Two images of at most `capacity` bytes, at `0` and at `capacity`. -/
def twoRegion (capacity : Nat) (enc : V → List UInt8) (dec : List UInt8 → Option V)
    (enc_le : ∀ v, (enc v).length ≤ capacity) (dec_enc : ∀ v, dec (enc v) = some v) :
    Format (Bool × Nat) V where
  reach := fun p a => tr.base capacity p ≤ a ∧ a < tr.base capacity p + min p.2 capacity
  readVal := fun f p =>
    dec ((List.range (min p.2 capacity)).map (fun i => f (tr.base capacity p + i)))
  alloc := fun p v => (!p.1, (enc v).length)
  writes := fun p v => imgWrites (tr.base capacity (!p.1, (enc v).length)) (enc v)
  frame := by
    intro f g p h
    congr 1
    refine List.ext_getElem (by simp) ?_
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    have h2' : i < min p.2 capacity := by simpa using h2
    exact h _ ⟨by omega, by omega⟩
  fresh := by
    intro p v a w hw ha
    have hb := mem_imgWrites _ _ _ _ hw
    have hle := enc_le v
    obtain ⟨h1, h2⟩ := ha
    have hm : min p.2 capacity ≤ capacity := Nat.min_le_right _ _
    cases hp : p.1
    · simp [tr.base, hp] at hb h1 h2
      omega
    · simp [tr.base, hp] at hb h1 h2
      omega
  correct := by
    intro f p v
    show dec _ = _
    have hmin : min (enc v).length capacity = (enc v).length := Nat.min_eq_left (enc_le v)
    show dec ((List.range (min (enc v).length capacity)).map _) = _
    rw [hmin]
    rw [show (List.range (enc v).length).map (fun i =>
        overlay f (imgWrites (tr.base capacity (!p.1, (enc v).length)) (enc v))
          (tr.base capacity (!p.1, (enc v).length) + i)) = enc v from ?_]
    · exact dec_enc v
    · refine List.ext_getElem (by simp) ?_
      intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      exact overlay_imgWrites_get (enc v) f _ i (by simpa using h2)

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
  [.write (F.writes r v), .flushUser, .setRoot (F.alloc r v), .flushUser]

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
  refine ⟨tinyDisk (false, 1), tinyDisk (true, 1), true, false,
    ⟨⟨rfl, rfl, rfl, rfl⟩, by decide⟩, ?_, by decide, by decide⟩
  refine ⟨fun a => Or.inl rfl, Or.inr ?_, rfl, rfl, rfl, rfl⟩
  show (true, 1) ∈ ([] ++ [] : List (Bool × Nat)) ++ [(true, 1)]
  simp

end RaftKV.Disk
