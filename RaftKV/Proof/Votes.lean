import RaftKV.Proof.Sends

/-!
# Vote discipline

Two facts about how a replica handles its vote, and they are what Election
Safety ultimately rests on:

* **`step_cfg`** — a node's configuration never changes, so a node's own id and
  the cluster membership are stable.
* **`votedFor_stable`** — a node cannot change its mind within a term. If its
  term is unchanged by an event, a vote already cast stays cast for the same
  candidate.

`handleRequestVote_grant` then extracts everything we need to know from the act
of granting a vote.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [KVStore κ]

@[simp] theorem maybeStepDown_cfg (s : NodeState σ κ) (t : Nat) (h : Option Nat) :
    (maybeStepDown s t h).1.cfg = s.cfg := by
  rw [maybeStepDown]; split <;> rfl

/-- **A replica's configuration is immutable.** -/
theorem step_cfg (s : NodeState σ κ) (ev : Event) : (Protocol.step s ev).1.cfg = s.cfg := by
  cases ev with
  | recv src m =>
      cases m with
      | requestVote term candId li lt =>
          rw [Protocol.step, handleRequestVote]
          split
          · rfl
          · dsimp only; split <;> simp
      | requestVoteResp term g =>
          rw [Protocol.step, handleRequestVoteResp]
          split
          · rfl
          · split
            · rfl
            · dsimp only; split <;> (split <;> simp)
      | appendEntries term l pi pt es lc =>
          rw [Protocol.step, handleAppendEntries]
          split
          · rfl
          · dsimp only; split
            · simp
            · dsimp only; simp
      | appendEntriesResp term ok mi =>
          rw [Protocol.step, handleAppendEntriesResp]
          split
          · rfl
          · split
            · rfl
            · split <;> simp
  | clientReq rid c =>
      rw [Protocol.step, handleClientReq]
      split
      · rfl
      · dsimp only; simp
  | electionTimeout =>
      rw [Protocol.step]; split
      · rfl
      · rw [startElection]; dsimp only; split <;> simp
  | heartbeatTimeout => rw [Protocol.step]; split <;> rfl

/--
**A vote, once cast, is not withdrawn within its term.**

Either the vote survives the event unchanged, or the event strictly advanced
the node's term — in which case the old vote is no longer about the same term
and Raft is free to forget it. Granting is the only operation that writes
`votedFor`, and its guard refuses to overwrite an existing vote for a different
candidate.
-/
theorem votedFor_step (s : NodeState σ κ) (ev : Event) (c : Nat)
    (hv : s.votedFor = some c) :
    (Protocol.step s ev).1.votedFor = some c
      ∨ s.currentTerm < (Protocol.step s ev).1.currentTerm := by
  cases ev with
  | recv src m =>
      cases m with
      | requestVote term candId li lt =>
          by_cases hgt : term > s.currentTerm
          · right
            rw [Protocol.step, handleRequestVote_term_eq]; omega
          · left
            rw [Protocol.step, handleRequestVote]
            split
            · exact hv
            · have hmsd : (maybeStepDown s term (none : Option Nat)).1 = s := by
                rw [maybeStepDown, if_neg hgt]
              dsimp only
              split
              · rename_i hfree
                rw [hmsd] at hfree ⊢
                rw [voteGranted] at hfree
                simp only [Bool.and_eq_true, beq_iff_eq] at hfree
                rw [hv] at hfree
                exact absurd hfree.1 (by simp)
              · rw [hmsd]; exact hv
      | requestVoteResp term g =>
          by_cases hgt : term > s.currentTerm
          · right
            rw [Protocol.step, handleRequestVoteResp_term_eq]; omega
          · left
            rw [Protocol.step, handleRequestVoteResp]
            rw [if_neg hgt]
            split
            · exact hv
            · dsimp only; split <;> (split <;> simpa using hv)
      | appendEntries term l pi pt es lc =>
          by_cases hgt : term > s.currentTerm
          · right
            rw [Protocol.step, handleAppendEntries_term_eq]; omega
          · left
            rw [Protocol.step, handleAppendEntries]
            split
            · exact hv
            · have hmsd : (maybeStepDown s term (some l)).1 = s := by
                rw [maybeStepDown, if_neg hgt]
              dsimp only
              rw [hmsd]
              split
              · simp [hv]
              · dsimp only; simp [hv]
      | appendEntriesResp term ok mi =>
          by_cases hgt : term > s.currentTerm
          · right
            rw [Protocol.step, handleAppendEntriesResp_term_eq]; omega
          · left
            rw [Protocol.step, handleAppendEntriesResp]
            rw [if_neg hgt]
            split
            · exact hv
            · split <;> simpa using hv
  | clientReq rid c' =>
      left
      rw [Protocol.step, handleClientReq]
      split
      · exact hv
      · dsimp only; simpa using hv
  | electionTimeout =>
      rw [Protocol.step]
      split
      · exact Or.inl hv
      · right; rw [startElection_term]; omega
  | heartbeatTimeout =>
      left; rw [Protocol.step]; split <;> exact hv

/--
**A grant requires an unspent vote.**

The guard reads `votedFor` *after* any step-down, so a node that grants either
moved into a strictly newer term — where its vote was reset — or had not voted
in the term it was already in.
-/
theorem handleRequestVote_grant_free {s : NodeState σ κ} {src term candId li lt to t : Nat}
    (h : Action.send to (Msg.requestVoteResp t true)
          ∈ (handleRequestVote s src term candId li lt).2) :
    s.currentTerm < term ∨ s.votedFor = none := by
  by_cases hlt : term < s.currentTerm
  · rw [handleRequestVote, if_pos hlt] at h
    exact absurd (Msg.requestVoteResp.inj (Action.send.inj (List.mem_singleton.mp h)).2).2
      (by simp)
  · by_cases hgt : s.currentTerm < term
    · exact Or.inl hgt
    · right
      have hmsd : (maybeStepDown s term (none : Option Nat)).1 = s := by
        rw [maybeStepDown, if_neg (by omega)]
      by_cases hg : voteGranted (maybeStepDown s term (none : Option Nat)).1 candId li lt
      · rw [hmsd, voteGranted] at hg
        simp only [Bool.and_eq_true, beq_iff_eq] at hg
        exact hg.1
      · exfalso
        rw [handleRequestVote, if_neg hlt] at h
        dsimp only at h
        rw [if_neg hg] at h
        rcases List.mem_append.mp h with h' | h'
        · exact absurd h' maybeStepDown_no_send
        · exact absurd
            (Msg.requestVoteResp.inj (Action.send.inj (List.mem_singleton.mp h')).2).2 (by simp)

/--
Everything Election Safety needs to know about the act of granting a vote: it
goes to the node that asked, it is stamped with the voter's *post*-event term,
and it is recorded in the voter's `votedFor`.
-/
theorem handleRequestVote_grant {s : NodeState σ κ} {src term candId li lt to t : Nat}
    (h : Action.send to (Msg.requestVoteResp t true)
          ∈ (handleRequestVote s src term candId li lt).2) :
    to = src
    ∧ (handleRequestVote s src term candId li lt).1.currentTerm = t
    ∧ (handleRequestVote s src term candId li lt).1.votedFor = some candId
    ∧ upToDate (handleRequestVote s src term candId li lt).1 li lt = true
    ∧ t = term := by
  by_cases hlt : term < s.currentTerm
  · rw [handleRequestVote, if_pos hlt] at h
    exact absurd (Msg.requestVoteResp.inj (Action.send.inj (List.mem_singleton.mp h)).2).2
      (by simp)
  · by_cases hg : voteGranted (maybeStepDown s term none).1 candId li lt
    · rw [handleRequestVote, if_neg hlt] at h ⊢
      dsimp only at h ⊢
      rw [if_pos hg] at h ⊢
      rcases List.mem_append.mp h with h' | h'
      · exact absurd h' maybeStepDown_no_send
      · have heq := List.mem_singleton.mp h'
        have ht : t = (maybeStepDown s term none).1.currentTerm :=
          (Msg.requestVoteResp.inj (Action.send.inj heq).2).1
        refine ⟨(Action.send.inj heq).1, ht.symm, rfl, ?_, ?_⟩
        · rw [voteGranted] at hg
          simpa [upToDate] using (Bool.and_eq_true _ _ |>.mp hg).2
        · rw [ht, maybeStepDown_term]; omega
    · rw [handleRequestVote, if_neg hlt] at h
      dsimp only at h
      rw [if_neg hg] at h
      rcases List.mem_append.mp h with h' | h'
      · exact absurd h' maybeStepDown_no_send
      · exact absurd (Msg.requestVoteResp.inj (Action.send.inj (List.mem_singleton.mp h')).2).2
          (by simp)

/-- The form used by the invariant proof: an unchanged term preserves the vote. -/
theorem votedFor_stable (s : NodeState σ κ) (ev : Event) (c : Nat)
    (hterm : (Protocol.step s ev).1.currentTerm = s.currentTerm)
    (hv : s.votedFor = some c) :
    (Protocol.step s ev).1.votedFor = some c := by
  rcases votedFor_step s ev c hv with h | h
  · exact h
  · omega

end RaftKV.Proof
