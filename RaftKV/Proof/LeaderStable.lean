import RaftKV.Proof.AppendProv

/-!
# A leader cannot be demoted within its own term

The global half of "a leader's log is append-only during its term".

A leader loses its role in exactly two ways: `stepDown`, which *strictly
increases* the term by construction; or `handleAppendEntries`, which demotes
unconditionally. The second is the dangerous one — it could demote a leader
without advancing its term, if a same-term `AppendEntries` could reach it.

No such message can exist. By `AEFromWinner` any term-`t` `appendEntries` was
sent by the winner of term `t`; by `everWinner_unique` that winner is the leader
itself; and by `PacketsNotSelf` a node never addresses a packet to itself.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [KVStore κ]

/-- Local form: given no same-term `AppendEntries`, a leader keeps its role and term. -/
theorem step_leader_demote {s : NodeState σ κ} {ev : Event}
    (hl : s.role = Role.leader)
    (hne : ∀ src t l pi pt es lc,
      ev = Event.recv src (Msg.appendEntries t l pi pt es lc) → t ≠ s.currentTerm)
    (hns : ∀ src t l li a ps,
      ev = Event.recv src (Msg.installSnapshot t l li a ps) → t ≠ s.currentTerm) :
    ((Protocol.step s ev).1.role = Role.leader
        ∧ (Protocol.step s ev).1.currentTerm = s.currentTerm)
      ∨ s.currentTerm < (Protocol.step s ev).1.currentTerm := by
  cases ev with
  | recv src m =>
      cases m with
      | requestVote term candId li lt =>
          by_cases hgt : term > s.currentTerm
          · right; rw [Protocol.step, handleRequestVote_term_eq]; omega
          · left
            rw [Protocol.step, handleRequestVote]
            by_cases hlt : term < s.currentTerm
            · rw [if_pos hlt]; exact ⟨hl, rfl⟩
            · have hmsd : (maybeStepDown s term none).1 = s := by
                rw [maybeStepDown, if_neg hgt]
              rw [if_neg hlt]
              dsimp only
              rw [hmsd]
              split <;> exact ⟨hl, rfl⟩
      | requestVoteResp term g =>
          by_cases hgt : term > s.currentTerm
          · right; rw [Protocol.step, handleRequestVoteResp_term_eq]; omega
          · left
            rw [Protocol.step, handleRequestVoteResp, if_neg hgt]
            rw [if_pos (by rw [hl]; simp)]
            exact ⟨hl, rfl⟩
      | appendEntries term l pi pt es lc =>
          have hterm : term ≠ s.currentTerm := hne src term l pi pt es lc rfl
          by_cases hgt : term > s.currentTerm
          · right; rw [Protocol.step, handleAppendEntries_term_eq]; omega
          · left
            have hlt : term < s.currentTerm := by omega
            rw [Protocol.step, handleAppendEntries, if_pos hlt]
            exact ⟨hl, rfl⟩
      | appendEntriesResp term ok mi =>
          by_cases hgt : term > s.currentTerm
          · right; rw [Protocol.step, handleAppendEntriesResp_term_eq]; omega
          · left
            rw [Protocol.step, handleAppendEntriesResp, if_neg hgt]
            by_cases hguard : s.role != Role.leader || term != s.currentTerm
            · rw [if_pos hguard]; exact ⟨hl, rfl⟩
            · rw [if_neg hguard]
              split
              · exact ⟨by simpa using hl, by simp⟩
              · exact ⟨by simpa using hl, by simp⟩
      | installSnapshot term lid li a ps =>
          -- a same-term snapshot cannot exist for the same reason a same-term
          -- `AppendEntries` cannot: it would have to come from this very leader
          by_cases hgt : term > s.currentTerm
          · right; rw [Protocol.step, handleInstallSnapshot_term_eq]; omega
          · by_cases hlt : term < s.currentTerm
            · left
              rw [Protocol.step, handleInstallSnapshot_stale s term lid li a ps hlt]
              exact ⟨hl, rfl⟩
            · exfalso
              exact hns src term lid li a ps rfl (by omega)
  | clientReq rid cmd =>
      left
      rw [Protocol.step, handleClientReq, if_neg (by rw [hl]; simp)]
      dsimp only
      exact ⟨by simpa using hl, by simp⟩
  | electionTimeout =>
      left
      rw [Protocol.step, if_pos (by rw [hl]; simp)]
      exact ⟨hl, rfl⟩
  | heartbeatTimeout =>
      left
      rw [Protocol.step]
      split <;> exact ⟨hl, rfl⟩


/--
**Campaigning always advances the term.**

`role := .candidate` is written in exactly one place, `startElection`, and that
site increments the term. So a node that is campaigning after a step either was
already campaigning, or has just moved to a strictly larger term. Together with
term monotonicity this is what stops a node from re-entering candidacy in a term
it has already led — including across a crash, which returns it as a follower.
-/
theorem step_candidate_term (s : NodeState σ κ) (ev : Event)
    (h : (Protocol.step s ev).1.role = Role.candidate) :
    s.role = Role.candidate ∨ s.currentTerm < (Protocol.step s ev).1.currentTerm := by
  cases ev with
  | recv src m =>
      cases m with
      | installSnapshot term lid li a ps =>
          left
          by_cases hlt : term < s.currentTerm
          · rw [Protocol.step, handleInstallSnapshot_stale s term lid li a ps hlt] at h
            exact h
          · rw [Protocol.step, handleInstallSnapshot_follower s term lid li a ps hlt] at h
            exact absurd h (by simp)
      | requestVote term candId li lt =>
          by_cases hgt : term > s.currentTerm
          · right; rw [Protocol.step, handleRequestVote_term_eq]; omega
          · left
            rw [Protocol.step, handleRequestVote] at h
            have hmsd : (maybeStepDown s term (none : Option Nat)).1 = s := by
              rw [maybeStepDown, if_neg hgt]
            split at h
            · exact h
            · dsimp only at h
              rw [hmsd] at h
              split at h
              · exact h
              · exact h
      | requestVoteResp term g =>
          by_cases hgt : term > s.currentTerm
          · right; rw [Protocol.step, handleRequestVoteResp_term_eq]; omega
          · left
            rw [Protocol.step, handleRequestVoteResp] at h
            split at h
            · exact absurd h (by simp [stepDown])
            · split at h
              · exact h
              · dsimp only at h
                split at h <;> (split at h <;> first | exact h | exact absurd h (by simp))
      | appendEntries term l pi pt es lc =>
          by_cases hgt : term > s.currentTerm
          · right; rw [Protocol.step, handleAppendEntries_term_eq]; omega
          · left
            rw [Protocol.step, handleAppendEntries] at h
            split at h
            · exact h
            · dsimp only at h
              split at h
              · exact absurd h (by simp)
              · dsimp only at h; exact absurd h (by simp)
      | appendEntriesResp term ok mi =>
          by_cases hgt : term > s.currentTerm
          · right; rw [Protocol.step, handleAppendEntriesResp_term_eq]; omega
          · left
            rw [Protocol.step, handleAppendEntriesResp] at h
            split at h
            · exact absurd h (by simp [stepDown])
            · split at h
              · exact h
              · split at h
                · simpa using h
                · exact h
  | clientReq rid cmd =>
      left
      rw [Protocol.step, handleClientReq] at h
      split at h
      · exact h
      · dsimp only at h; simpa using h
  | electionTimeout =>
      right
      rw [Protocol.step] at h ⊢
      split at h
      · exact absurd h (by rename_i hq; rw [(by simpa using hq : s.role = Role.leader)]; simp)
      · rename_i hq; rw [if_neg hq, startElection_term]; omega
  | heartbeatTimeout =>
      left
      rw [Protocol.step] at h
      split at h
      · exact h
      · exact h

/--
**A leader keeps its role for as long as its term is unchanged.**

Equivalently: leadership of term `t` is a single contiguous stretch — a node
cannot leave and re-enter leadership of the same term.

A crash is the one exception, and it is a benign one: the node comes back a
follower in the same term, but its log is durable and therefore untouched. That
is the third disjunct, and `log_stable_in_term` below is what the callers of
this lemma actually want.
-/
theorem leader_stable {members : List Nat} {w w' : World σ κ} [LawfulLogStore σ]
    (hnd : members.Nodup) (hr : Reachable members w) (hs : Step members w w') {i : Nat}
    (hl : (w.nodes i).role = Role.leader) :
    ((w'.nodes i).role = Role.leader
        ∧ (w'.nodes i).currentTerm = (w.nodes i).currentTerm)
      ∨ (w.nodes i).currentTerm < (w'.nodes i).currentTerm
      ∨ (w'.full i = w.full i
          ∧ (w'.nodes i).currentTerm = (w.nodes i).currentTerm) := by
  have hp := pInv_reachable hr
  -- A same-term `AppendEntries` addressed to a term-`t` leader cannot exist.
  have hno : ∀ src t l pi pt es lc,
      (src, i, Msg.appendEntries t l pi pt es lc) ∈ w.sent → t ≠ (w.nodes i).currentTerm := by
    intro src t l pi pt es lc hmem hteq
    have hwin : WonTerm members w src t := hp.aeWinner src i t l pi pt es lc hmem
    have hself : i = src := leader_is_unique_winner hnd hr hl hteq.symm hwin
    exact hp.notSelf (src, i, Msg.appendEntries t l pi pt es lc) hmem (by simp [hself])
  have hnos : ∀ src t l li (a : Entry) (ps : List (String × String)),
      (src, i, Msg.installSnapshot t l li a ps) ∈ w.sent → t ≠ (w.nodes i).currentTerm := by
    intro src t l li a ps hmem hteq
    have hwin : WonTerm members w src t := hp.snapWinner src i t l li a ps hmem
    have hself : i = src := leader_is_unique_winner hnd hr hl hteq.symm hwin
    exact hp.notSelf (src, i, Msg.installSnapshot t l li a ps) hmem (by simp [hself])
  cases hs with
  | deliver s d m hd hmem =>
      by_cases hij : i = d
      · subst hij
        rw [act_nodes_self]
        refine Or.imp id Or.inl (step_leader_demote hl ?_ ?_)
        · intro src t l pi pt es lc heq
          have h1 : s = src := (Event.recv.inj heq).1
          have h2 : m = Msg.appendEntries t l pi pt es lc := (Event.recv.inj heq).2
          subst h2; subst h1
          exact hno _ t l pi pt es lc hmem
        · intro src t l li a ps heq
          have h1 : s = src := (Event.recv.inj heq).1
          have h2 : m = Msg.installSnapshot t l li a ps := (Event.recv.inj heq).2
          subst h2; subst h1
          exact hnos _ t l li a ps hmem
      · rw [act_nodes_ne _ _ _ hij]; exact Or.inl ⟨hl, rfl⟩
  | electionTimeout k _ =>
      by_cases hij : i = k
      · subst hij
        rw [act_nodes_self]
        exact Or.imp id Or.inl (step_leader_demote hl
          (fun _ _ _ _ _ _ _ hq => Event.noConfusion hq)
          (fun _ _ _ _ _ _ hq => Event.noConfusion hq))
      · rw [act_nodes_ne _ _ _ hij]; exact Or.inl ⟨hl, rfl⟩
  | heartbeat k _ =>
      by_cases hij : i = k
      · subst hij
        rw [act_nodes_self]
        exact Or.imp id Or.inl (step_leader_demote hl
          (fun _ _ _ _ _ _ _ hq => Event.noConfusion hq)
          (fun _ _ _ _ _ _ hq => Event.noConfusion hq))
      · rw [act_nodes_ne _ _ _ hij]; exact Or.inl ⟨hl, rfl⟩
  | client k rid cmd _ =>
      by_cases hij : i = k
      · subst hij
        rw [act_nodes_self]
        exact Or.imp id Or.inl (step_leader_demote hl
          (fun _ _ _ _ _ _ _ hq => Event.noConfusion hq)
          (fun _ _ _ _ _ _ hq => Event.noConfusion hq))
      · rw [act_nodes_ne _ _ _ hij]; exact Or.inl ⟨hl, rfl⟩
  | crash k _ =>
      by_cases hij : i = k
      · subst hij
        rw [crash_nodes_self]
        exact Or.inr (Or.inr ⟨rfl, restart_currentTerm _⟩)
      · rw [crash_nodes_ne _ _ hij]; exact Or.inl ⟨hl, rfl⟩
  | compact k _ =>
      -- compaction keeps the node exactly where it was, logically
      by_cases hij : i = k
      · subst hij
        rw [compactAt_nodes_self]
        exact Or.inl ⟨by simpa using hl, by simp⟩
      · rw [compactAt_nodes_ne _ _ hij]; exact Or.inl ⟨hl, rfl⟩

end RaftKV.Proof
