import RaftKV.Proof.StepLemmas

/-!
# Terms never go backwards

The first genuine invariant, and the backbone of every later argument: a
replica's `currentTerm` is monotonically non-decreasing across every possible
event.

Raft's safety story is fundamentally an induction over terms, so almost nothing
else can be proved until this is settled.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [KVStore κ]

theorem maybeStepDown_term (s : NodeState σ κ) (t : Nat) (h : Option Nat) :
    (maybeStepDown s t h).1.currentTerm = max s.currentTerm t := by
  rw [maybeStepDown]; split <;> simp <;> omega

theorem maybeStepDown_term_le (s : NodeState σ κ) (t : Nat) (h : Option Nat) :
    s.currentTerm ≤ (maybeStepDown s t h).1.currentTerm := by
  rw [maybeStepDown_term]; omega

theorem handleRequestVote_term (s : NodeState σ κ) (src term candId li lt : Nat) :
    s.currentTerm ≤ (handleRequestVote s src term candId li lt).1.currentTerm := by
  rw [handleRequestVote]
  split
  · exact Nat.le_refl _
  · dsimp only
    have h := maybeStepDown_term s term (none : Option Nat)
    split <;> simp <;> omega

theorem handleRequestVoteResp_term (s : NodeState σ κ) (term : Nat) (g : Bool) (src : Nat) :
    s.currentTerm ≤ (handleRequestVoteResp s term g src).1.currentTerm := by
  rw [handleRequestVoteResp]
  split
  · rename_i h; simp; omega
  · split
    · exact Nat.le_refl _
    · dsimp only; split <;> (split <;> simp)

theorem handleAppendEntries_term (s : NodeState σ κ)
    (src term leaderId prevIdx prevTerm : Nat) (es : List Entry) (lc : Nat) :
    s.currentTerm ≤ (handleAppendEntries s src term leaderId prevIdx prevTerm es lc).1.currentTerm := by
  rw [handleAppendEntries]
  split
  · exact Nat.le_refl _
  · dsimp only
    have h := maybeStepDown_term s term (some leaderId)
    split
    · simp; omega
    · dsimp only; simp; omega

theorem handleAppendEntriesResp_term (s : NodeState σ κ)
    (src term : Nat) (success : Bool) (matchIdx : Nat) :
    s.currentTerm ≤ (handleAppendEntriesResp s src term success matchIdx).1.currentTerm := by
  rw [handleAppendEntriesResp]
  split
  · rename_i h; simp; omega
  · split
    · exact Nat.le_refl _
    · split <;> simp

theorem handleClientReq_term (s : NodeState σ κ) (rid : Nat) (c : Command) :
    (handleClientReq s rid c).1.currentTerm = s.currentTerm := by
  rw [handleClientReq]
  split
  · rfl
  · dsimp only; simp

theorem startElection_term (s : NodeState σ κ) :
    (startElection s).1.currentTerm = s.currentTerm + 1 := by
  rw [startElection]; dsimp only; split <;> simp

/-! ### Exact term equations

Sharper than monotonicity: each message handler leaves the term at exactly
`max` of the old term and the term carried by the message. These make the later
case analyses decidable by `omega` rather than by hand.
-/

theorem handleRequestVote_term_eq (s : NodeState σ κ) (src term candId li lt : Nat) :
    (handleRequestVote s src term candId li lt).1.currentTerm = max s.currentTerm term := by
  rw [handleRequestVote]
  split
  · rename_i h; simp; omega
  · dsimp only
    have h := maybeStepDown_term s term (none : Option Nat)
    split <;> simp [h]

theorem handleRequestVoteResp_term_eq (s : NodeState σ κ) (term : Nat) (g : Bool) (src : Nat) :
    (handleRequestVoteResp s term g src).1.currentTerm = max s.currentTerm term := by
  rw [handleRequestVoteResp]
  split
  · rename_i h; simp; omega
  · rename_i h
    split
    · simp; omega
    · dsimp only; split <;> (split <;> simp <;> omega)

theorem handleAppendEntries_term_eq (s : NodeState σ κ)
    (src term leaderId prevIdx prevTerm : Nat) (es : List Entry) (lc : Nat) :
    (handleAppendEntries s src term leaderId prevIdx prevTerm es lc).1.currentTerm
      = max s.currentTerm term := by
  rw [handleAppendEntries]
  split
  · rename_i h; simp; omega
  · dsimp only
    have h := maybeStepDown_term s term (some leaderId)
    split
    · simp [h]
    · dsimp only; simp [h]

/--
**Accepting a leader's authority spends the term's vote.**

A follower that does not reject an `appendEntries` outright adopts the sender as
the holder of its vote for the term, if it had not already voted. This is what
makes a node that has heard from a leader unable to vote again in that term.
-/
theorem handleAppendEntries_votedFor_ne (s : NodeState σ κ)
    (src term leaderId prevIdx prevTerm : Nat) (es : List Entry) (lc : Nat)
    (h : s.currentTerm ≤ term) :
    (handleAppendEntries s src term leaderId prevIdx prevTerm es lc).1.votedFor ≠ none := by
  rw [handleAppendEntries, if_neg (by omega)]
  dsimp only
  split
  · simp
  · dsimp only; simp

theorem handleAppendEntriesResp_term_eq (s : NodeState σ κ)
    (src term : Nat) (ok : Bool) (mi : Nat) :
    (handleAppendEntriesResp s src term ok mi).1.currentTerm = max s.currentTerm term := by
  rw [handleAppendEntriesResp]
  split
  · rename_i h; simp; omega
  · rename_i h
    split
    · simp; omega
    · split <;> simp <;> omega

/--
**Terms are monotone.** No event can lower a replica's `currentTerm`.
-/
theorem step_term_mono (s : NodeState σ κ) (ev : Event) :
    s.currentTerm ≤ (Protocol.step s ev).1.currentTerm := by
  cases ev with
  | recv src m =>
      cases m with
      | requestVote t c li lt => exact handleRequestVote_term s src t c li lt
      | requestVoteResp t g => exact handleRequestVoteResp_term s t g src
      | appendEntries t l pi pt es lc => exact handleAppendEntries_term s src t l pi pt es lc
      | appendEntriesResp t ok mi => exact handleAppendEntriesResp_term s src t ok mi
  | clientReq rid c => rw [Protocol.step, handleClientReq_term]; exact Nat.le_refl _
  | electionTimeout =>
      show s.currentTerm ≤ (if s.role == Role.leader then (s, []) else startElection s).1.currentTerm
      split
      · exact Nat.le_refl _
      · rw [startElection_term]; omega
  | heartbeatTimeout =>
      show s.currentTerm ≤ (if s.role == Role.leader then (s, broadcastAppend s) else (s, [])).1.currentTerm
      split <;> exact Nat.le_refl _

/-- Acting on one node never lowers any node's term. -/
theorem act_term_mono (w : World σ κ) (j : Nat) (ev : Event) (i : Nat) :
    (w.nodes i).currentTerm ≤ ((w.act j ev).nodes i).currentTerm := by
  rw [World.act]; dsimp only; split
  · rename_i he; subst he; exact step_term_mono _ _
  · exact Nat.le_refl _

/-- Terms are monotone at every node across a world step. -/
theorem world_term_mono {members : List Nat} {w w' : World σ κ} (h : Step members w w') (i : Nat) :
    (w.nodes i).currentTerm ≤ (w'.nodes i).currentTerm := by
  cases h with
  | deliver src dst m _ _ => exact act_term_mono _ _ _ _
  | electionTimeout j _ => exact act_term_mono _ _ _ _
  | heartbeat j _ => exact act_term_mono _ _ _ _
  | client j rid cmd _ => exact act_term_mono _ _ _ _
  | crash j _ => exact crash_term_mono _ _ _
  | compact j _ => exact compact_term_mono _ _ _

end RaftKV.Proof
