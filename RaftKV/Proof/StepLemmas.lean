import RaftKV.Protocol.Network

/-!
# Structural lemmas about `step`

Small facts about which fields each helper can and cannot disturb. They are
dull individually, but they are what makes the invariant proofs in
`RaftKV.Proof.Election` manageable: most branches of `step` are dispatched by
observing that they simply cannot touch the field under discussion.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [KVStore κ]

/-! ## Applying committed entries changes only the state machine -/

@[simp] theorem applyOne_currentTerm (s : NodeState σ κ) :
    (applyOne s).1.currentTerm = s.currentTerm := by
  rw [applyOne]; cases LogStore.get s.log (s.lastApplied + 1) <;> rfl

@[simp] theorem applyOne_role (s : NodeState σ κ) :
    (applyOne s).1.role = s.role := by
  rw [applyOne]; cases LogStore.get s.log (s.lastApplied + 1) <;> rfl

@[simp] theorem applyOne_votedFor (s : NodeState σ κ) :
    (applyOne s).1.votedFor = s.votedFor := by
  rw [applyOne]; cases LogStore.get s.log (s.lastApplied + 1) <;> rfl

@[simp] theorem applyOne_log (s : NodeState σ κ) :
    (applyOne s).1.log = s.log := by
  rw [applyOne]; cases LogStore.get s.log (s.lastApplied + 1) <;> rfl

@[simp] theorem applyOne_cfg (s : NodeState σ κ) :
    (applyOne s).1.cfg = s.cfg := by
  rw [applyOne]; cases LogStore.get s.log (s.lastApplied + 1) <;> rfl

@[simp] theorem applyOne_votesGranted (s : NodeState σ κ) :
    (applyOne s).1.votesGranted = s.votesGranted := by
  rw [applyOne]; cases LogStore.get s.log (s.lastApplied + 1) <;> rfl

@[simp] theorem applyLoop_votesGranted (f : Nat) (s : NodeState σ κ) (acc : List Action) :
    (applyLoop f s acc).1.votesGranted = s.votesGranted := by
  induction f generalizing s acc with
  | zero => rfl
  | succ n ih => rw [applyLoop]; split <;> simp [ih]

@[simp] theorem applyCommitted_votesGranted (s : NodeState σ κ) :
    (applyCommitted s).1.votesGranted = s.votesGranted := by
  simp [applyCommitted]

@[simp] theorem advanceCommit_votesGranted (s : NodeState σ κ) :
    (advanceCommit s).votesGranted = s.votesGranted := by
  rw [advanceCommit]; split <;> rfl

@[simp] theorem becomeLeader_votesGranted (s : NodeState σ κ) :
    (becomeLeader s).1.votesGranted = s.votesGranted := rfl

@[simp] theorem stepDown_votesGranted (s : NodeState σ κ) (t : Nat) (h : Option Nat) :
    (stepDown s t h).1.votesGranted = [] := rfl

@[simp] theorem applyOne_commitIndex (s : NodeState σ κ) :
    (applyOne s).1.commitIndex = s.commitIndex := by
  rw [applyOne]; cases LogStore.get s.log (s.lastApplied + 1) <;> rfl

@[simp] theorem applyLoop_commitIndex (f : Nat) (s : NodeState σ κ) (acc : List Action) :
    (applyLoop f s acc).1.commitIndex = s.commitIndex := by
  induction f generalizing s acc with
  | zero => rfl
  | succ n ih => rw [applyLoop]; split <;> simp [ih]

@[simp] theorem applyOne_lastApplied_ge (s : NodeState σ κ) :
    s.lastApplied ≤ (applyOne s).1.lastApplied := by
  rw [applyOne]; split
  · exact Nat.le_refl _
  · exact Nat.le_succ _

theorem applyLoop_lastApplied_ge (f : Nat) (s : NodeState σ κ) (acc : List Action) :
    s.lastApplied ≤ (applyLoop f s acc).1.lastApplied := by
  induction f generalizing s acc with
  | zero => exact Nat.le_refl _
  | succ n ih =>
      rw [applyLoop]
      split
      · exact Nat.le_trans (applyOne_lastApplied_ge s) (ih _ _)
      · exact Nat.le_refl _

theorem applyCommitted_lastApplied_ge (s : NodeState σ κ) :
    s.lastApplied ≤ (applyCommitted s).1.lastApplied := applyLoop_lastApplied_ge _ _ _

@[simp] theorem applyOne_snapIndex (s : NodeState σ κ) :
    (applyOne s).1.snapIndex = s.snapIndex := by
  rw [applyOne]; split <;> rfl

@[simp] theorem applyOne_snapKV (s : NodeState σ κ) :
    (applyOne s).1.snapKV = s.snapKV := by
  rw [applyOne]; split <;> rfl

@[simp] theorem applyLoop_snapKV (f : Nat) (s : NodeState σ κ) (acc : List Action) :
    (applyLoop f s acc).1.snapKV = s.snapKV := by
  induction f generalizing s acc with
  | zero => rfl
  | succ n ih =>
      rw [applyLoop]
      split
      · rw [ih]; exact applyOne_snapKV s
      · rfl

@[simp] theorem applyCommitted_snapKV (s : NodeState σ κ) :
    (applyCommitted s).1.snapKV = s.snapKV := applyLoop_snapKV _ _ _

@[simp] theorem applyLoop_snapIndex (f : Nat) (s : NodeState σ κ) (acc : List Action) :
    (applyLoop f s acc).1.snapIndex = s.snapIndex := by
  induction f generalizing s acc with
  | zero => rfl
  | succ n ih =>
      rw [applyLoop]
      split
      · rw [ih]; exact applyOne_snapIndex s
      · rfl

@[simp] theorem applyCommitted_snapIndex (s : NodeState σ κ) :
    (applyCommitted s).1.snapIndex = s.snapIndex := applyLoop_snapIndex _ _ _

@[simp] theorem applyOne_snapSessions (s : NodeState σ κ) :
    (applyOne s).1.snapSessions = s.snapSessions := by
  rw [applyOne]; split <;> rfl

@[simp] theorem applyLoop_snapSessions (f : Nat) (s : NodeState σ κ) (acc : List Action) :
    (applyLoop f s acc).1.snapSessions = s.snapSessions := by
  induction f generalizing s acc with
  | zero => rfl
  | succ n ih =>
      rw [applyLoop]
      split
      · rw [ih]; exact applyOne_snapSessions s
      · rfl

@[simp] theorem applyCommitted_snapSessions (s : NodeState σ κ) :
    (applyCommitted s).1.snapSessions = s.snapSessions := applyLoop_snapSessions _ _ _

@[simp] theorem applyCommitted_commitIndex (s : NodeState σ κ) :
    (applyCommitted s).1.commitIndex = s.commitIndex := by
  simp [applyCommitted]

@[simp] theorem applyOne_matchIndex (s : NodeState σ κ) :
    (applyOne s).1.matchIndex = s.matchIndex := by
  rw [applyOne]; cases LogStore.get s.log (s.lastApplied + 1) <;> rfl

@[simp] theorem applyLoop_matchIndex (f : Nat) (s : NodeState σ κ) (acc : List Action) :
    (applyLoop f s acc).1.matchIndex = s.matchIndex := by
  induction f generalizing s acc with
  | zero => rfl
  | succ n ih => rw [applyLoop]; split <;> simp [ih]

@[simp] theorem applyCommitted_matchIndex (s : NodeState σ κ) :
    (applyCommitted s).1.matchIndex = s.matchIndex := by
  simp [applyCommitted]

@[simp] theorem advanceCommit_matchIndex (s : NodeState σ κ) :
    (advanceCommit s).matchIndex = s.matchIndex := by
  rw [advanceCommit]; split <;> rfl

@[simp] theorem applyLoop_cfg (f : Nat) (s : NodeState σ κ) (acc : List Action) :
    (applyLoop f s acc).1.cfg = s.cfg := by
  induction f generalizing s acc with
  | zero => rfl
  | succ n ih => rw [applyLoop]; split <;> simp [ih]

@[simp] theorem applyCommitted_cfg (s : NodeState σ κ) :
    (applyCommitted s).1.cfg = s.cfg := by
  simp [applyCommitted]

@[simp] theorem advanceCommit_cfg (s : NodeState σ κ) :
    (advanceCommit s).cfg = s.cfg := by
  rw [advanceCommit]; split <;> rfl

@[simp] theorem becomeLeader_cfg (s : NodeState σ κ) :
    (becomeLeader s).1.cfg = s.cfg := rfl

@[simp] theorem stepDown_cfg (s : NodeState σ κ) (t : Nat) (h : Option Nat) :
    (stepDown s t h).1.cfg = s.cfg := rfl

@[simp] theorem applyLoop_currentTerm (f : Nat) (s : NodeState σ κ) (acc : List Action) :
    (applyLoop f s acc).1.currentTerm = s.currentTerm := by
  induction f generalizing s acc with
  | zero => rfl
  | succ n ih => rw [applyLoop]; split <;> simp [ih]

@[simp] theorem applyLoop_role (f : Nat) (s : NodeState σ κ) (acc : List Action) :
    (applyLoop f s acc).1.role = s.role := by
  induction f generalizing s acc with
  | zero => rfl
  | succ n ih => rw [applyLoop]; split <;> simp [ih]

@[simp] theorem applyLoop_votedFor (f : Nat) (s : NodeState σ κ) (acc : List Action) :
    (applyLoop f s acc).1.votedFor = s.votedFor := by
  induction f generalizing s acc with
  | zero => rfl
  | succ n ih => rw [applyLoop]; split <;> simp [ih]

@[simp] theorem applyLoop_log (f : Nat) (s : NodeState σ κ) (acc : List Action) :
    (applyLoop f s acc).1.log = s.log := by
  induction f generalizing s acc with
  | zero => rfl
  | succ n ih => rw [applyLoop]; split <;> simp [ih]

@[simp] theorem applyCommitted_currentTerm (s : NodeState σ κ) :
    (applyCommitted s).1.currentTerm = s.currentTerm := by
  simp [applyCommitted]

@[simp] theorem applyCommitted_role (s : NodeState σ κ) :
    (applyCommitted s).1.role = s.role := by
  simp [applyCommitted]

@[simp] theorem applyCommitted_votedFor (s : NodeState σ κ) :
    (applyCommitted s).1.votedFor = s.votedFor := by
  simp [applyCommitted]

@[simp] theorem applyCommitted_log (s : NodeState σ κ) :
    (applyCommitted s).1.log = s.log := by
  simp [applyCommitted]

/-! ## Advancing the commit index changes only the commit index -/

@[simp] theorem advanceCommit_currentTerm (s : NodeState σ κ) :
    (advanceCommit s).currentTerm = s.currentTerm := by
  rw [advanceCommit]; split <;> rfl

@[simp] theorem advanceCommit_role (s : NodeState σ κ) :
    (advanceCommit s).role = s.role := by
  rw [advanceCommit]; split <;> rfl

@[simp] theorem advanceCommit_votedFor (s : NodeState σ κ) :
    (advanceCommit s).votedFor = s.votedFor := by
  rw [advanceCommit]; split <;> rfl

@[simp] theorem advanceCommit_log (s : NodeState σ κ) :
    (advanceCommit s).log = s.log := by
  rw [advanceCommit]; split <;> rfl

/-! ## Becoming leader keeps the term and the vote -/

@[simp] theorem becomeLeader_currentTerm (s : NodeState σ κ) :
    (becomeLeader s).1.currentTerm = s.currentTerm := rfl

@[simp] theorem becomeLeader_votedFor (s : NodeState σ κ) :
    (becomeLeader s).1.votedFor = s.votedFor := rfl

@[simp] theorem becomeLeader_log (s : NodeState σ κ) :
    (becomeLeader s).1.log = s.log := rfl

@[simp] theorem becomeLeader_role (s : NodeState σ κ) :
    (becomeLeader s).1.role = Role.leader := rfl

/-! ## Stepping down -/

@[simp] theorem stepDown_currentTerm (s : NodeState σ κ) (t : Nat) (h : Option Nat) :
    (stepDown s t h).1.currentTerm = t := rfl

@[simp] theorem stepDown_votedFor (s : NodeState σ κ) (t : Nat) (h : Option Nat) :
    (stepDown s t h).1.votedFor = none := rfl

@[simp] theorem stepDown_role (s : NodeState σ κ) (t : Nat) (h : Option Nat) :
    (stepDown s t h).1.role = Role.follower := rfl

@[simp] theorem stepDown_log (s : NodeState σ κ) (t : Nat) (h : Option Nat) :
    (stepDown s t h).1.log = s.log := rfl

/-! ## What a client append does to the log -/

/-- On a leader, `handleClientReq` appends exactly the client's entry. -/
theorem handleClientReq_log {s : NodeState σ κ} {rid : Nat} {cmd : Command}
    (hl : s.role = Role.leader) :
    (handleClientReq s rid cmd).1.log
      = LogStore.append s.log { term := s.currentTerm, cmd := cmd, reqId := rid } := by
  rw [handleClientReq, if_neg (by rw [hl]; simp)]
  dsimp only
  simp

/-- ...and leaves the term alone. -/
theorem handleClientReq_term_eq {s : NodeState σ κ} {rid : Nat} {cmd : Command} :
    (handleClientReq s rid cmd).1.currentTerm = s.currentTerm := by
  rw [handleClientReq]; split
  · rfl
  · dsimp only; simp


/-- The state machine never runs ahead of the commit index. -/
theorem applyLoop_applied_le (f : Nat) (s : NodeState σ κ) (acc : List Action)
    (h : s.lastApplied ≤ s.commitIndex) :
    (applyLoop f s acc).1.lastApplied ≤ (applyLoop f s acc).1.commitIndex := by
  induction f generalizing s acc with
  | zero => rw [applyLoop]; exact h
  | succ n ih =>
      rw [applyLoop]
      split
      · rename_i hlt
        refine ih _ _ ?_
        show (applyOne s).1.lastApplied ≤ (applyOne s).1.commitIndex
        rw [applyOne_commitIndex, applyOne]
        cases LogStore.get s.log (s.lastApplied + 1) with
        | none => exact h
        | some e => dsimp only; omega
      · exact h

theorem applyCommitted_applied_le (s : NodeState σ κ) (h : s.lastApplied ≤ s.commitIndex) :
    (applyCommitted s).1.lastApplied ≤ (applyCommitted s).1.commitIndex :=
  applyLoop_applied_le _ s [] h


@[simp] theorem becomeLeader_lastApplied (s : NodeState σ κ) :
    (becomeLeader s).1.lastApplied = s.lastApplied := rfl

@[simp] theorem becomeLeader_commitIndex (s : NodeState σ κ) :
    (becomeLeader s).1.commitIndex = s.commitIndex := rfl

/-! ### The snapshot handler -/

/-- A stale snapshot changes nothing at all. -/
theorem handleInstallSnapshot_stale (s : NodeState σ κ)
    (term leaderId lastIdx : Nat) (a : Entry) (ps : List (String × String) × List Nat)
    (h : term < s.currentTerm) :
    handleInstallSnapshot s term leaderId lastIdx a ps = (s, []) := by
  rw [handleInstallSnapshot, if_pos h]

/-- Any other snapshot leaves the receiver a follower — it is leader contact. -/
theorem handleInstallSnapshot_follower (s : NodeState σ κ)
    (term leaderId lastIdx : Nat) (a : Entry) (ps : List (String × String) × List Nat)
    (h : ¬ (term < s.currentTerm)) :
    (handleInstallSnapshot s term leaderId lastIdx a ps).1.role = Role.follower := by
  rw [handleInstallSnapshot, if_neg h]
  dsimp only
  split <;> rfl

/-- A snapshot that is not installed leaves the log and the snapshot alone. -/
theorem handleInstallSnapshot_noop (s : NodeState σ κ)
    (term leaderId lastIdx : Nat) (a : Entry) (ps : List (String × String) × List Nat)
    (hi : Protocol.snapInstalls s term lastIdx a = false) :
    (handleInstallSnapshot s term leaderId lastIdx a ps).1.log = s.log
      ∧ (handleInstallSnapshot s term leaderId lastIdx a ps).1.snapIndex = s.snapIndex
      ∧ (handleInstallSnapshot s term leaderId lastIdx a ps).1.lastApplied = s.lastApplied
      ∧ (handleInstallSnapshot s term leaderId lastIdx a ps).1.commitIndex = s.commitIndex := by
  have hmsd : ∀ v, ((maybeStepDown s term v).1.log = s.log
      ∧ (maybeStepDown s term v).1.snapIndex = s.snapIndex
      ∧ (maybeStepDown s term v).1.lastApplied = s.lastApplied
      ∧ (maybeStepDown s term v).1.commitIndex = s.commitIndex) := by
    intro v; rw [maybeStepDown]; split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  rw [handleInstallSnapshot]
  by_cases hlt : term < s.currentTerm
  · rw [if_pos hlt]; exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [if_neg hlt]
    dsimp only
    rw [if_neg (by simp [hi])]
    exact hmsd (some leaderId)

/-- The snapshot handler never touches the configuration. -/
@[simp] theorem handleInstallSnapshot_cfg (s : NodeState σ κ)
    (term leaderId lastIdx : Nat) (a : Entry) (ps : List (String × String) × List Nat) :
    (handleInstallSnapshot s term leaderId lastIdx a ps).1.cfg = s.cfg := by
  rw [handleInstallSnapshot]
  split
  · rfl
  · dsimp only
    have hc : (maybeStepDown s term (some leaderId)).1.cfg = s.cfg := by
      rw [maybeStepDown]; split <;> rfl
    split <;> exact hc

@[simp] theorem advanceCommit_lastApplied (s : NodeState σ κ) :
    (advanceCommit s).lastApplied = s.lastApplied := by
  rw [advanceCommit]; split <;> rfl

/-- Advancing the commit index only ever moves it forward. -/
theorem advanceCommit_ge (s : NodeState σ κ) : s.commitIndex ≤ (advanceCommit s).commitIndex := by
  rcases hq : (commitCandidates s).head? with _ | n
  · rw [advanceCommit, hq]; exact Nat.le_refl _
  · have hmem : n ∈ commitCandidates s := List.mem_of_mem_head? hq
    rw [commitCandidates] at hmem
    have hok : commitOk s n = true := (List.mem_filter.mp (List.mem_reverse.mp hmem)).2
    rw [commitOk] at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
    rw [advanceCommit, hq]
    exact Nat.le_of_lt hok.1.1

/-- Applying and advancing keeps the state machine behind the commit index. -/
theorem step_applied_le (s : NodeState σ κ) (ev : Event) (h : s.lastApplied ≤ s.commitIndex) :
    (Protocol.step s ev).1.lastApplied ≤ (Protocol.step s ev).1.commitIndex := by
  cases ev with
  | recv src m =>
      cases m with
      | requestVote term c li lt =>
          rw [Protocol.step, handleRequestVote]
          split
          · exact h
          · dsimp only
            have hd : (maybeStepDown s term (none : Option Nat)).1.lastApplied
                ≤ (maybeStepDown s term (none : Option Nat)).1.commitIndex := by
              rw [maybeStepDown]; split <;> exact h
            split <;> simpa using hd
      | requestVoteResp term g =>
          rw [Protocol.step, handleRequestVoteResp]
          split
          · exact h
          · split
            · exact h
            · dsimp only
              split <;> (split <;> simpa using h)
      | appendEntries term l pi pt es lc =>
          rw [Protocol.step, handleAppendEntries]
          split
          · exact h
          · dsimp only
            have hd : (maybeStepDown s term (some l)).1.lastApplied
                ≤ (maybeStepDown s term (some l)).1.commitIndex := by
              rw [maybeStepDown]; split <;> exact h
            split
            · simpa using hd
            · dsimp only
              refine applyCommitted_applied_le _ ?_
              simp only []
              omega
      | appendEntriesResp term ok mi =>
          rw [Protocol.step, handleAppendEntriesResp]
          split
          · exact h
          · split
            · exact h
            · split
              · refine applyCommitted_applied_le _ ?_
                rw [advanceCommit_lastApplied]
                refine Nat.le_trans ?_ (advanceCommit_ge _)
                simpa using h
              · exact h
      | installSnapshot term l li a ps =>
          rw [Protocol.step, handleInstallSnapshot]
          split
          · exact h
          · dsimp only
            have hd : (maybeStepDown s term (some l)).1.lastApplied
                ≤ (maybeStepDown s term (some l)).1.commitIndex := by
              rw [maybeStepDown]; split <;> exact h
            split
            · exact Nat.le_refl _
            · simpa using hd
  | clientReq rid cmd =>
      rw [Protocol.step, handleClientReq]
      split
      · exact h
      · dsimp only
        refine applyCommitted_applied_le _ ?_
        rw [advanceCommit_lastApplied]
        refine Nat.le_trans ?_ (advanceCommit_ge _)
        simpa using h
  | electionTimeout =>
      rw [Protocol.step]
      split
      · exact h
      · rw [startElection]; dsimp only; split <;> simpa using h
  | heartbeatTimeout =>
      rw [Protocol.step]; split <;> exact h


@[simp] theorem stepDown_kv (s : NodeState σ κ) (t : Nat) (h : Option Nat) :
    (stepDown s t h).1.kv = s.kv := rfl

@[simp] theorem stepDown_lastApplied (s : NodeState σ κ) (t : Nat) (h : Option Nat) :
    (stepDown s t h).1.lastApplied = s.lastApplied := rfl

@[simp] theorem stepDown_log' (s : NodeState σ κ) (t : Nat) (h : Option Nat) :
    (stepDown s t h).1.log = s.log := rfl

@[simp] theorem maybeStepDown_kv (s : NodeState σ κ) (t : Nat) (h : Option Nat) :
    (maybeStepDown s t h).1.kv = s.kv := by rw [maybeStepDown]; split <;> rfl

@[simp] theorem maybeStepDown_lastApplied (s : NodeState σ κ) (t : Nat) (h : Option Nat) :
    (maybeStepDown s t h).1.lastApplied = s.lastApplied := by
  rw [maybeStepDown]; split <;> rfl

@[simp] theorem maybeStepDown_log (s : NodeState σ κ) (t : Nat) (h : Option Nat) :
    (maybeStepDown s t h).1.log = s.log := by rw [maybeStepDown]; split <;> rfl

@[simp] theorem becomeLeader_kv (s : NodeState σ κ) : (becomeLeader s).1.kv = s.kv := rfl

@[simp] theorem advanceCommit_kv (s : NodeState σ κ) : (advanceCommit s).kv = s.kv := by
  rw [advanceCommit]; split <;> rfl

@[simp] theorem stepDown_sessions (s : NodeState σ κ) (t : Nat) (h : Option Nat) :
    (stepDown s t h).1.sessions = s.sessions := rfl

@[simp] theorem maybeStepDown_sessions (s : NodeState σ κ) (t : Nat) (h : Option Nat) :
    (maybeStepDown s t h).1.sessions = s.sessions := by rw [maybeStepDown]; split <;> rfl

@[simp] theorem becomeLeader_sessions (s : NodeState σ κ) :
    (becomeLeader s).1.sessions = s.sessions := rfl

@[simp] theorem advanceCommit_sessions (s : NodeState σ κ) :
    (advanceCommit s).sessions = s.sessions := by rw [advanceCommit]; split <;> rfl


/--
`aeAccepts` is exactly the condition on which `handleAppendEntries` splices.

Stated so the ghost logical log in `RaftKV.Protocol.Network` can be defined
against one copy of the branch conditions rather than a second that could drift.
-/
theorem handleAppendEntries_accepts (s : NodeState σ κ)
    (src term leaderId prevIdx prevTerm : Nat) (entries : List Entry) (leaderCommit : Nat) :
    (handleAppendEntries s src term leaderId prevIdx prevTerm entries leaderCommit).1.log
      = if aeAccepts s term prevIdx prevTerm then appendFrom s.log (prevIdx + 1) entries
        else s.log := by
  rw [handleAppendEntries]
  have hmsd : (maybeStepDown s term (some leaderId)).1.log = s.log := by
    rw [maybeStepDown]; split <;> rfl
  unfold aeAccepts
  split
  · rename_i hlt
    rw [if_neg (by simp [hlt])]
  · rename_i hlt
    dsimp only
    cases hac : aeConsistent s prevIdx prevTerm
    · simp [hac, hmsd]
    · simp [hac, hlt, hmsd, applyCommitted_log]


/-- The companion for the commit index: it moves exactly when the splice happens. -/
theorem handleAppendEntries_commit (s : NodeState σ κ)
    (src term leaderId prevIdx prevTerm : Nat) (entries : List Entry) (leaderCommit : Nat) :
    (handleAppendEntries s src term leaderId prevIdx prevTerm entries leaderCommit).1.commitIndex
      = if aeAccepts s term prevIdx prevTerm then
          max s.commitIndex
            (min leaderCommit (LogStore.lastIndex (appendFrom s.log (prevIdx + 1) entries)))
        else s.commitIndex := by
  rw [handleAppendEntries]
  have hmsd : (maybeStepDown s term (some leaderId)).1.log = s.log := by
    rw [maybeStepDown]; split <;> rfl
  have hmsc : (maybeStepDown s term (some leaderId)).1.commitIndex = s.commitIndex := by
    rw [maybeStepDown]; split <;> rfl
  unfold aeAccepts
  split
  · rename_i hlt
    rw [if_neg (by simp [hlt])]
  · rename_i hlt
    dsimp only
    cases hac : aeConsistent s prevIdx prevTerm
    · simp [hac, hmsc]
    · simp [hac, hlt, hmsd, hmsc]

end RaftKV.Proof