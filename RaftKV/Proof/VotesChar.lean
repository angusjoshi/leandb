import RaftKV.Proof.Votes

/-!
# How a step can change the vote tally

The key structural lemma behind the leader invariant. It says that a node which
is campaigning or leading *after* an event got there in exactly one of two ways:

* it just started an election, so its tally is precisely its own self-vote; or
* it was already campaigning or leading, its term is unchanged, and its tally
  either did not move or gained exactly the sender of a grant it just received.

Everything else — appending entries, answering a client, heartbeating, granting
a vote to someone else — leaves the tally alone or demotes the node to
follower.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [KVStore κ]

/-- The two ways to hold a non-follower role after an event. -/
theorem step_votes_char {s : NodeState σ κ} {ev : Event}
    (hne : (Protocol.step s ev).1.role ≠ Role.follower) :
    (ev = Event.electionTimeout
      ∧ (Protocol.step s ev).1.votesGranted = [s.cfg.me]
      ∧ (Protocol.step s ev).1.votedFor = some s.cfg.me)
    ∨ (s.role ≠ Role.follower
      ∧ (Protocol.step s ev).1.currentTerm = s.currentTerm
      ∧ ((Protocol.step s ev).1.votesGranted = s.votesGranted
         ∨ ∃ src term, ev = Event.recv src (Msg.requestVoteResp term true)
             ∧ term = s.currentTerm
             ∧ src ∉ s.votesGranted
             ∧ (Protocol.step s ev).1.votesGranted = src :: s.votesGranted)) := by
  cases ev with
  | recv src m =>
      cases m with
      | requestVote term candId li lt =>
          right
          rw [Protocol.step, handleRequestVote] at hne ⊢
          by_cases hlt : term < s.currentTerm
          · rw [if_pos hlt] at hne ⊢
            exact ⟨hne, rfl, Or.inl rfl⟩
          · by_cases hgt : term > s.currentTerm
            · exfalso
              rw [if_neg hlt] at hne
              dsimp only at hne
              have hr : (maybeStepDown s term none).1.role = Role.follower := by
                rw [maybeStepDown, if_pos hgt]; rfl
              revert hne; split <;> simp [hr]
            · have hmsd : (maybeStepDown s term none).1 = s := by
                rw [maybeStepDown, if_neg hgt]
              rw [if_neg hlt] at hne ⊢
              dsimp only at hne ⊢
              rw [hmsd] at hne ⊢
              split at hne
              · rename_i hg; rw [if_pos hg]; exact ⟨hne, rfl, Or.inl rfl⟩
              · rename_i hg; rw [if_neg hg]; exact ⟨hne, rfl, Or.inl rfl⟩
      | requestVoteResp term g =>
          right
          rw [Protocol.step, handleRequestVoteResp] at hne ⊢
          by_cases hgt : term > s.currentTerm
          · exact absurd rfl (by rw [if_pos hgt] at hne; exact hne)
          · rw [if_neg hgt] at hne ⊢
            by_cases hguard : s.role != Role.candidate || term != s.currentTerm || !g
            · rw [if_pos hguard] at hne ⊢
              exact ⟨hne, rfl, Or.inl rfl⟩
            · rw [if_neg hguard] at hne ⊢
              simp only [Bool.not_eq_true, Bool.or_eq_false_iff, bne_eq_false_iff_eq,
                Bool.not_eq_false] at hguard
              obtain ⟨⟨hrole, hterm⟩, hgtrue'⟩ := hguard
              have hgtrue : g = true := by
                cases g
                · exact absurd hgtrue' (by simp)
                · rfl
              subst hgtrue
              refine ⟨by rw [hrole]; exact fun h => Role.noConfusion h, ?_, ?_⟩
              · dsimp only; split <;> (split <;> rfl)
              · dsimp only
                by_cases hmem : s.votesGranted.contains src
                · left; rw [if_pos hmem]; split <;> rfl
                · right
                  refine ⟨src, term, rfl, hterm, ?_, by rw [if_neg hmem]; split <;> rfl⟩
                  intro hcon
                  exact hmem (by simpa using hcon)
      | appendEntries term l pi pt es lc =>
          right
          rw [Protocol.step, handleAppendEntries] at hne ⊢
          by_cases hlt : term < s.currentTerm
          · rw [if_pos hlt] at hne ⊢
            exact ⟨hne, rfl, Or.inl rfl⟩
          · exfalso
            rw [if_neg hlt] at hne
            dsimp only at hne
            revert hne
            split
            · simp
            · dsimp only; simp
      | appendEntriesResp term ok mi =>
          right
          rw [Protocol.step, handleAppendEntriesResp] at hne ⊢
          by_cases hgt : term > s.currentTerm
          · exact absurd rfl (by rw [if_pos hgt] at hne; exact hne)
          · rw [if_neg hgt] at hne ⊢
            by_cases hguard : s.role != Role.leader || term != s.currentTerm
            · rw [if_pos hguard] at hne ⊢
              exact ⟨hne, rfl, Or.inl rfl⟩
            · rw [if_neg hguard] at hne ⊢
              simp only [Bool.not_eq_true, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hguard
              refine ⟨by rw [hguard.1]; exact fun h => Role.noConfusion h, ?_, ?_⟩
              · split <;> simp
              · left; split <;> simp
      | installSnapshot term l li a ps =>
          right
          by_cases hlt : term < s.currentTerm
          · rw [Protocol.step, handleInstallSnapshot_stale s term l li a ps hlt] at hne ⊢
            exact ⟨hne, rfl, Or.inl rfl⟩
          · exfalso
            rw [Protocol.step] at hne
            exact hne (handleInstallSnapshot_follower s term l li a ps hlt)
  | clientReq rid cmd =>
      right
      rw [Protocol.step, handleClientReq] at hne ⊢
      by_cases hguard : s.role != Role.leader
      · rw [if_pos hguard] at hne ⊢
        exact ⟨hne, rfl, Or.inl rfl⟩
      · rw [if_neg hguard] at hne ⊢
        simp only [bne_eq_false_iff_eq, Bool.not_eq_true] at hguard
        refine ⟨by rw [hguard]; exact fun h => Role.noConfusion h, ?_, ?_⟩
        · dsimp only; simp
        · left; dsimp only; simp
  | electionTimeout =>
      rw [Protocol.step] at hne ⊢
      by_cases hl : s.role == Role.leader
      · right
        rw [if_pos hl] at hne ⊢
        exact ⟨hne, rfl, Or.inl rfl⟩
      · left
        rw [if_neg hl] at hne ⊢
        rw [startElection]
        dsimp only
        refine ⟨rfl, ?_, ?_⟩ <;> (split <;> rfl)
  | heartbeatTimeout =>
      right
      rw [Protocol.step] at hne ⊢
      split at hne
      · rename_i hg; rw [if_pos hg]; exact ⟨hne, rfl, Or.inl rfl⟩
      · rename_i hg; rw [if_neg hg]; exact ⟨hne, rfl, Or.inl rfl⟩

/--
A node that is leading after an event either was already leading with an
unchanged tally, or has just had its tally checked against a majority.

This is what lets `QuorumInv` be inductive: leadership is only ever *created*
at the two sites that test `isMajority`.
-/
theorem step_leader_quorum {s : NodeState σ κ} {ev : Event}
    (hl : (Protocol.step s ev).1.role = Role.leader) :
    (s.role = Role.leader ∧ (Protocol.step s ev).1.votesGranted = s.votesGranted)
    ∨ s.cfg.isMajority (Protocol.step s ev).1.votesGranted = true := by
  cases ev with
  | recv src m =>
      cases m with
      | requestVote term candId li lt =>
          left
          rw [Protocol.step, handleRequestVote] at hl ⊢
          by_cases hlt : term < s.currentTerm
          · rw [if_pos hlt] at hl ⊢; exact ⟨hl, rfl⟩
          · by_cases hgt : term > s.currentTerm
            · exfalso
              rw [if_neg hlt] at hl
              dsimp only at hl
              have hr : (maybeStepDown s term none).1.role = Role.follower := by
                rw [maybeStepDown, if_pos hgt]; rfl
              revert hl; split <;> simp [hr]
            · have hmsd : (maybeStepDown s term none).1 = s := by
                rw [maybeStepDown, if_neg hgt]
              rw [if_neg hlt] at hl ⊢
              dsimp only at hl ⊢
              rw [hmsd] at hl ⊢
              split at hl
              · rename_i hg; rw [if_pos hg]; exact ⟨hl, rfl⟩
              · rename_i hg; rw [if_neg hg]; exact ⟨hl, rfl⟩
      | requestVoteResp term g =>
          rw [Protocol.step, handleRequestVoteResp] at hl ⊢
          by_cases hgt : term > s.currentTerm
          · exfalso; rw [if_pos hgt, stepDown_role] at hl; exact Role.noConfusion hl
          · rw [if_neg hgt] at hl ⊢
            by_cases hguard : s.role != Role.candidate || term != s.currentTerm || !g
            · left; rw [if_pos hguard] at hl ⊢; exact ⟨hl, rfl⟩
            · right
              rw [if_neg hguard] at hl ⊢
              simp only [Bool.not_eq_true, Bool.or_eq_false_iff, bne_eq_false_iff_eq,
                Bool.not_eq_false] at hguard
              obtain ⟨⟨hrole, _⟩, _⟩ := hguard
              dsimp only at hl ⊢
              by_cases hmem : s.votesGranted.contains src = true
              · rw [if_pos hmem] at hl ⊢
                by_cases hmaj : s.cfg.isMajority s.votesGranted = true
                · rw [if_pos hmaj]; simpa using hmaj
                · exfalso; rw [if_neg hmaj] at hl; simp [hrole] at hl
              · rw [if_neg hmem] at hl ⊢
                by_cases hmaj : s.cfg.isMajority (src :: s.votesGranted) = true
                · rw [if_pos hmaj]; simpa using hmaj
                · exfalso; rw [if_neg hmaj] at hl; simp [hrole] at hl
      | appendEntries term l pi pt es lc =>
          left
          rw [Protocol.step, handleAppendEntries] at hl ⊢
          by_cases hlt : term < s.currentTerm
          · rw [if_pos hlt] at hl ⊢; exact ⟨hl, rfl⟩
          · exfalso
            rw [if_neg hlt] at hl
            dsimp only at hl
            revert hl
            split
            · simp
            · dsimp only; simp
      | appendEntriesResp term ok mi =>
          left
          rw [Protocol.step, handleAppendEntriesResp] at hl ⊢
          by_cases hgt : term > s.currentTerm
          · exfalso; rw [if_pos hgt, stepDown_role] at hl; exact Role.noConfusion hl
          · rw [if_neg hgt] at hl ⊢
            by_cases hguard : s.role != Role.leader || term != s.currentTerm
            · rw [if_pos hguard] at hl ⊢; exact ⟨hl, rfl⟩
            · rw [if_neg hguard] at hl ⊢
              simp only [Bool.not_eq_true, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hguard
              refine ⟨hguard.1, ?_⟩
              split <;> simp
      | installSnapshot term l li a ps =>
          left
          by_cases hlt : term < s.currentTerm
          · rw [Protocol.step, handleInstallSnapshot_stale s term l li a ps hlt] at hl ⊢
            exact ⟨hl, rfl⟩
          · exfalso
            rw [Protocol.step, handleInstallSnapshot_follower s term l li a ps hlt] at hl
            exact Role.noConfusion hl
  | clientReq rid cmd =>
      left
      rw [Protocol.step, handleClientReq] at hl ⊢
      by_cases hguard : s.role != Role.leader
      · rw [if_pos hguard] at hl ⊢; exact ⟨hl, rfl⟩
      · rw [if_neg hguard] at hl ⊢
        simp only [bne_eq_false_iff_eq, Bool.not_eq_true] at hguard
        refine ⟨hguard, ?_⟩
        dsimp only; simp
  | electionTimeout =>
      rw [Protocol.step] at hl ⊢
      by_cases hlead : s.role == Role.leader
      · left; rw [if_pos hlead] at hl ⊢; exact ⟨hl, rfl⟩
      · right
        rw [if_neg hlead] at hl ⊢
        rw [startElection] at hl ⊢
        dsimp only at hl ⊢
        by_cases hmaj : s.cfg.isMajority [s.cfg.me] = true
        · rw [if_pos hmaj]; simpa using hmaj
        · exfalso; rw [if_neg hmaj] at hl; simp at hl
  | heartbeatTimeout =>
      left
      rw [Protocol.step] at hl ⊢
      split at hl
      · rename_i hg; rw [if_pos hg]; exact ⟨hl, rfl⟩
      · rename_i hg; rw [if_neg hg]; exact ⟨hl, rfl⟩

end RaftKV.Proof
