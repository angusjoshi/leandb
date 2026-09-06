import RaftKV.Proof.Ghost
import RaftKV.Proof.Leader

/-!
# At most one node ever wins a term

`Proof.electionSafety` says at most one node *currently* believes it leads term
`t`. That is a statement about the present, and it evaporates the moment the
term-`t` leader dies — precisely when log-level reasoning still needs to know
who won term `t`.

`WonTerm` is the durable version: it asserts a quorum of term-`t` votes for `i`
exists in the ghost history. Since that history only grows, **once true it stays
true forever**, and `wonTerm_unique` shows at most one node can ever satisfy it
for a given term.

This is the anchor for Log Matching and everything above it: it is what licenses
speaking of *"the"* term-`t` leader's log even after that leader is gone.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [KVStore κ]

/-- Node `i` assembled a quorum of term-`t` votes at some point in the past. -/
def WonTerm (members : List Nat) (w : World σ κ) (i t : Nat) : Prop :=
  ∃ V : List Nat, V.Nodup ∧ (∀ v ∈ V, v ∈ members)
    ∧ V.length ≥ members.length / 2 + 1
    ∧ ∀ v ∈ V, (v, i, t) ∈ w.votes

/-- Winning is permanent: the ghost history never shrinks. -/
theorem wonTerm_act {members : List Nat} {w : World σ κ} {i t : Nat}
    (h : WonTerm members w i t) (j : Nat) (ev : Event) :
    WonTerm members (w.act j ev) i t := by
  obtain ⟨V, h1, h2, h3, h4⟩ := h
  exact ⟨V, h1, h2, h3, fun v hv => by rw [act_votes]; exact List.mem_append_left _ (h4 v hv)⟩

theorem wonTerm_step {members : List Nat} {w w' : World σ κ} {i t : Nat}
    (h : WonTerm members w i t) (hs : Step members w w') : WonTerm members w' i t := by
  cases hs with
  | deliver src dst m _ _ => exact wonTerm_act h _ _
  | electionTimeout k _ => exact wonTerm_act h _ _
  | heartbeat k _ => exact wonTerm_act h _ _
  | client k rid cmd _ => exact wonTerm_act h _ _
  | crash k _ =>
      obtain ⟨V, h1, h2, h3, h4⟩ := h
      exact ⟨V, h1, h2, h3, fun v hv => by rw [crash_votes]; exact h4 v hv⟩
  | compact k _ =>
      obtain ⟨V, h1, h2, h3, h4⟩ := h
      exact ⟨V, h1, h2, h3, fun v hv => by rw [compactAt_votes]; exact h4 v hv⟩

/-- A node that currently leads term `t` has won term `t`. -/
theorem wonTerm_of_leader {members : List Nat} {w : World σ κ}
    (hv : VotesInv members w) (hq : QuorumInv members w) (hg : GInv members w)
    {i : Nat} (hi : (w.nodes i).role = Role.leader) :
    WonTerm members w i (w.nodes i).currentTerm := by
  obtain ⟨hself, hnd, hsub, hwit⟩ :=
    hv i (by rw [hi]; exact fun h => Role.noConfusion h)
  refine ⟨(w.nodes i).votesGranted, hnd, hsub, hq i hi, ?_⟩
  intro v hv'
  rcases hwit v hv' with heq | hpkt
  · -- the node's own self-vote, which lives only in `votedFor`
    rw [heq]
    exact hg.selfRec i i hself
  · -- a grant that travelled on the wire
    exact hg.recorded v i _ hpkt

/--
**At most one node ever wins a term.**

Two winners of term `t` would hold quorums of term-`t` votes; those quorums
intersect, and the shared voter cast at most one term-`t` vote in the ghost
history — self-votes included.
-/
theorem wonTerm_unique {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hu : GVoteUnique w) {i j t : Nat}
    (h₁ : WonTerm members w i t) (h₂ : WonTerm members w j t) : i = j := by
  obtain ⟨V₁, hnd₁, hsub₁, hlen₁, hwit₁⟩ := h₁
  obtain ⟨V₂, hnd₂, hsub₂, hlen₂, hwit₂⟩ := h₂
  let c : Config := { me := i, members := members }
  obtain ⟨v, hv₁, hv₂⟩ :=
    quorum_intersect (c := c) hnd ⟨hnd₁, hsub₁, hlen₁⟩ ⟨hnd₂, hsub₂, hlen₂⟩
  exact hu v i j t (hwit₁ v hv₁) (hwit₂ v hv₂)

/-! ## Assembling the full invariant -/

/-- Everything proved about a reachable world, in one bundle. -/
structure AllInv (members : List Nat) (w : World σ κ) : Prop where
  /-- Wire-level vote accounting. -/
  base : Inv members w
  /-- Leader bookkeeping. -/
  leader : FullInv members w
  /-- Ghost vote history. -/
  ghost : GInv members w

theorem allInv_reachable {members : List Nat} {w : World σ κ} (h : Reachable members w) :
    AllInv members w := by
  induction h with
  | init => exact ⟨inv_init members, fullInv_init members, gInv_init members⟩
  | tail hr hs ih =>
      exact ⟨inv_step ih.base hs, fullInv_step ih.leader hs, gInv_step ih.base ih.ghost hs⟩

/--
**Election Safety, in its durable form.**

In any reachable world, at most one node has *ever* won a given term. Unlike
`electionSafety`, this survives the death of the leader in question, which is
what makes it usable as the foundation for log-level safety.
-/
theorem everWinner_unique {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) {i j t : Nat}
    (h₁ : WonTerm members w i t) (h₂ : WonTerm members w j t) : i = j :=
  wonTerm_unique hnd (allInv_reachable h).ghost.unique h₁ h₂

/-- Consequently, a node that leads term `t` is the unique winner of term `t`. -/
theorem leader_is_unique_winner {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) {i j t : Nat}
    (hi : (w.nodes i).role = Role.leader) (hit : (w.nodes i).currentTerm = t)
    (hj : WonTerm members w j t) : i = j := by
  have ha := allInv_reachable h
  exact everWinner_unique hnd h
    (hit ▸ wonTerm_of_leader ha.leader.votes ha.leader.quorum ha.ghost hi) hj

end RaftKV.Proof
