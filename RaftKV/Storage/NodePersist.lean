import RaftKV.Storage.Persist
import RaftKV.Storage.Bytes
import RaftKV.Protocol.Network

/-!
# The device justifies the crash rule

`RaftKV.Protocol.Step` has a `crash` rule that says the durable trio survives a
restart. That rule is an *assumption about the implementation*, and this file
discharges it: on the device modelled in `RaftKV.Storage.Disk`, with the
copy-on-write commit of `RaftKV.Storage.Persist`, a crash at any point leaves
the device holding a `Persistent σ` that rebuilds to exactly the node the model
says it should — the one before the commit, or the one after it.

Together with `Format.commit_crash_safe` this is the whole story:

* the model may crash a node at any step, and every safety theorem survives;
* the implementation may crash at any *byte* of a commit, and what it comes back
  with is always one of the two node states the model allows.

What is left assumed, and stated as such, is the device's single-word atomicity
and the shim's obligation to commit before it sends.
-/

namespace RaftKV.Disk

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [KVStore κ]

/--
**The device gives back a node the model allows.**

If the device holds node `s`'s durable projection and a commit of `s'`'s is in
progress, then after a crash at any point, recovery yields a durable state that
rebuilds to `Protocol.restart s` or to `Protocol.restart s'` — the two outcomes
`World.crash` permits, and nothing else.
-/
theorem crash_recovers_node (F : Format α (Persistent σ)) {d : Disk α}
    (s s' : NodeState σ κ) (hcfg : s'.cfg = s.cfg)
    (h : F.Holds d (persistOf s)) (k : Nat) {d' : Disk α}
    (hc : Crash (runOps d ((F.commitOps d.readRoot (persistOf s')).take k)) d') :
    (∃ p, F.recover d' = some p ∧ (recoverNode s.cfg p : NodeState σ κ) = Protocol.restart s)
      ∨ (∃ p, F.recover d' = some p
          ∧ (recoverNode s.cfg p : NodeState σ κ) = Protocol.restart s') := by
  rcases F.recover_crash h k hc with hr | hr
  · exact Or.inl ⟨persistOf s, hr, rfl⟩
  · exact Or.inr ⟨persistOf s', hr, by rw [restart_eq_recoverNode, hcfg]⟩

/--
**A completed commit leaves the node's own state on the device.**

So the invariant the shim maintains — "the device holds this node's durable
projection" — is re-established by every commit, which is what makes the theorem
above apply again to the next one.
-/
theorem commit_holds_node (F : Format α (Persistent σ)) {d : Disk α}
    (s s' : NodeState σ κ) (h : F.Holds d (persistOf s)) :
    F.Holds (runOps d (F.commitOps d.readRoot (persistOf s'))) (persistOf s') :=
  F.commit_holds h


/-! ## The concrete store

Two regions holding byte images of a node's durable trio, with the root cell
naming the live side and its length. Everything below `Format` is proved: the
encoding round-trips (`RaftKV.ByteCodec`), and the commit is crash-safe on the
torn-write device (`Format.commit_crash_safe`).

The capacity bound is the one deployment obligation: the log must fit in a
region. Lifting it is exactly what a copy-on-write B-tree instance would do —
same commit theorem, an allocator that hands out free pages instead of flipping
a bit — and that is also what log compaction wants.
-/

/-- The two-region store for a node's durable state. -/
def nodeFormat (capacity : Nat)
    (hfit : ∀ p : Persistent ArrayLog, (ByteCodec.enc p).length ≤ capacity) :
    Format (Bool × Nat) (Persistent ArrayLog) :=
  twoRegion capacity ByteCodec.enc (fun bs => (ByteCodec.dec bs).map Prod.fst) hfit
    (by intro v; rw [ByteCodec.dec_enc_nil]; rfl)

/--
**End to end for the store: a crash during a commit rebuilds a node the model
allows.**

Specialised to the concrete format, so nothing is left abstract: real bytes on a
device that tears, and the outcome is always one of the two node states
`World.crash` permits.
-/
theorem nodeFormat_crash_recovers {capacity : Nat}
    (hfit : ∀ p : Persistent ArrayLog, (ByteCodec.enc p).length ≤ capacity)
    {d : Disk (Bool × Nat)} (s s' : NodeState ArrayLog κ) (hcfg : s'.cfg = s.cfg)
    (h : (nodeFormat capacity hfit).Holds d (persistOf s)) (k : Nat) {d' : Disk (Bool × Nat)}
    (hc : Crash (runOps d
      (((nodeFormat capacity hfit).commitOps d.readRoot (persistOf s')).take k)) d') :
    (∃ p, (nodeFormat capacity hfit).recover d' = some p
        ∧ (recoverNode s.cfg p : NodeState ArrayLog κ) = Protocol.restart s)
      ∨ (∃ p, (nodeFormat capacity hfit).recover d' = some p
        ∧ (recoverNode s.cfg p : NodeState ArrayLog κ) = Protocol.restart s') :=
  crash_recovers_node _ s s' hcfg h k hc


end RaftKV.Disk
