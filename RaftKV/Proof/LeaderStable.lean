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
      ev = Event.recv src (Msg.appendEntries t l pi pt es lc) → t ≠ s.currentTerm) :
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
              split <;> exact ⟨by simpa using hl, by simp⟩
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
**A leader keeps its role for as long as its term is unchanged.**

Equivalently: leadership of term `t` is a single contiguous stretch — a node
cannot leave and re-enter leadership of the same term. This is what licenses
treating "the term-`t` leader's log" as a single, monotonically growing object.
-/
theorem leader_stable {members : List Nat} {w w' : World σ κ}
    (hnd : members.Nodup) (hr : Reachable members w) (hs : Step members w w') {i : Nat}
    (hl : (w.nodes i).role = Role.leader) :
    ((w'.nodes i).role = Role.leader
        ∧ (w'.nodes i).currentTerm = (w.nodes i).currentTerm)
      ∨ (w.nodes i).currentTerm < (w'.nodes i).currentTerm := by
  have hp := pInv_reachable hr
  -- A same-term `AppendEntries` addressed to a term-`t` leader cannot exist.
  have hno : ∀ src t l pi pt es lc,
      (src, i, Msg.appendEntries t l pi pt es lc) ∈ w.sent → t ≠ (w.nodes i).currentTerm := by
    intro src t l pi pt es lc hmem hteq
    have hwin : WonTerm members w src t := hp.aeWinner src i t l pi pt es lc hmem
    have hself : i = src := leader_is_unique_winner hnd hr hl hteq.symm hwin
    exact hp.notSelf (src, i, Msg.appendEntries t l pi pt es lc) hmem (by simp [hself])
  cases hs with
  | deliver s d m hd hmem =>
      by_cases hij : i = d
      · subst hij
        rw [act_nodes_self]
        refine step_leader_demote hl ?_
        intro src t l pi pt es lc heq
        have h1 : s = src := (Event.recv.inj heq).1
        have h2 : m = Msg.appendEntries t l pi pt es lc := (Event.recv.inj heq).2
        subst h2; subst h1
        exact hno _ t l pi pt es lc hmem
      · rw [act_nodes_ne _ _ _ hij]; exact Or.inl ⟨hl, rfl⟩
  | electionTimeout k _ =>
      by_cases hij : i = k
      · subst hij
        rw [act_nodes_self]
        exact step_leader_demote hl (fun _ _ _ _ _ _ _ hq => Event.noConfusion hq)
      · rw [act_nodes_ne _ _ _ hij]; exact Or.inl ⟨hl, rfl⟩
  | heartbeat k _ =>
      by_cases hij : i = k
      · subst hij
        rw [act_nodes_self]
        exact step_leader_demote hl (fun _ _ _ _ _ _ _ hq => Event.noConfusion hq)
      · rw [act_nodes_ne _ _ _ hij]; exact Or.inl ⟨hl, rfl⟩
  | client k rid cmd _ =>
      by_cases hij : i = k
      · subst hij
        rw [act_nodes_self]
        exact step_leader_demote hl (fun _ _ _ _ _ _ _ hq => Event.noConfusion hq)
      · rw [act_nodes_ne _ _ _ hij]; exact Or.inl ⟨hl, rfl⟩

/--
**A leader's log grows monotonically for as long as it leads.**

Combining `leader_stable` with `step_log_of_leader`: while a node holds
leadership across a step, its log is either untouched or extended by exactly one
entry — never truncated, never rewritten.
-/
theorem leader_log_monotone {members : List Nat} {w w' : World σ κ}
    [LawfulLogStore σ]
    (hs : Step members w w') {i : Nat}
    (hl : (w.nodes i).role = Role.leader)
    (hl' : (w'.nodes i).role = Role.leader) :
    (w'.nodes i).log = (w.nodes i).log
      ∨ ∃ e, (w'.nodes i).log = LogStore.append (w.nodes i).log e := by
  cases hs with
  | deliver s d m hd hmem =>
      by_cases hij : i = d
      · subst hij
        rw [act_nodes_self] at hl' ⊢
        exact step_log_of_leader _ _ hl hl'
      · rw [act_nodes_ne _ _ _ hij]; exact Or.inl rfl
  | electionTimeout k _ =>
      by_cases hij : i = k
      · subst hij
        rw [act_nodes_self] at hl' ⊢
        exact step_log_of_leader _ _ hl hl'
      · rw [act_nodes_ne _ _ _ hij]; exact Or.inl rfl
  | heartbeat k _ =>
      by_cases hij : i = k
      · subst hij
        rw [act_nodes_self] at hl' ⊢
        exact step_log_of_leader _ _ hl hl'
      · rw [act_nodes_ne _ _ _ hij]; exact Or.inl rfl
  | client k rid cmd _ =>
      by_cases hij : i = k
      · subst hij
        rw [act_nodes_self] at hl' ⊢
        exact step_log_of_leader _ _ hl hl'
      · rw [act_nodes_ne _ _ _ hij]; exact Or.inl rfl

end RaftKV.Proof
