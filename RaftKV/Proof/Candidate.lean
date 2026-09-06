import RaftKV.Proof.Elected

/-!
# A candidate's log stands still

Two local facts about candidacy, both needed to connect the log a candidate
*advertises* in its `requestVote` to the log it is eventually *elected* with:

* `candidate_log_stable` — while a node is a candidate its log cannot change.
  Only `handleClientReq` and `appendFrom` touch a log, and the first demands
  leadership while the second demotes to follower.
* `candidate_term_grows` — becoming a candidate strictly advances the term, so
  a node cannot re-enter candidacy in a term it has already campaigned in.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [LawfulLogStore σ] [KVStore κ]

/-- A leader never becomes a candidate; it can only stay or fall to follower. -/
theorem leader_not_to_candidate {s : NodeState σ κ} {ev : Event}
    (hl : s.role = Role.leader) : (Protocol.step s ev).1.role ≠ Role.candidate := by
  cases ev with
  | recv src m =>
      cases m with
      | installSnapshot term lid li a ps =>
          by_cases hlt : term < s.currentTerm
          · rw [Protocol.step, handleInstallSnapshot_stale s term lid li a ps hlt, hl]
            exact fun h => Role.noConfusion h
          · rw [Protocol.step, handleInstallSnapshot_follower s term lid li a ps hlt]
            exact fun h => Role.noConfusion h
      | requestVote term candId li lt =>
          rw [Protocol.step, handleRequestVote]
          split
          · rw [hl]; exact fun h => Role.noConfusion h
          · dsimp only
            by_cases hgt : term > s.currentTerm
            · have hr : (maybeStepDown s term none).1.role = Role.follower := by
                rw [maybeStepDown, if_pos hgt]; rfl
              split <;> simp [hr]
            · have hmsd : (maybeStepDown s term none).1 = s := by
                rw [maybeStepDown, if_neg hgt]
              rw [hmsd]; split <;> (simp [hl])
      | requestVoteResp term g =>
          rw [Protocol.step, handleRequestVoteResp]
          split
          · simp
          · rw [if_pos (by rw [hl]; simp)]; rw [hl]; exact fun h => Role.noConfusion h
      | appendEntries term l pi pt es lc =>
          rw [Protocol.step, handleAppendEntries]
          split
          · rw [hl]; exact fun h => Role.noConfusion h
          · dsimp only; split
            · simp
            · dsimp only; simp
      | appendEntriesResp term ok mi =>
          rw [Protocol.step, handleAppendEntriesResp]
          split
          · simp
          · split
            · rw [hl]; exact fun h => Role.noConfusion h
            · split <;> simp [hl]
  | clientReq rid cmd =>
      rw [Protocol.step, handleClientReq]
      split
      · rw [hl]; exact fun h => Role.noConfusion h
      · dsimp only; simp [hl]
  | electionTimeout =>
      rw [Protocol.step, if_pos (by rw [hl]; simp)]
      rw [hl]; exact fun h => Role.noConfusion h
  | heartbeatTimeout =>
      rw [Protocol.step]; split <;> (rw [hl]; exact fun h => Role.noConfusion h)

/-- **A candidate's log does not move.** -/
theorem candidate_log_stable {s : NodeState σ κ} {ev : Event}
    (h : (Protocol.step s ev).1.role = Role.candidate) :
    (Protocol.step s ev).1.log = s.log := by
  rcases step_log s ev with hl | ⟨rid, cmd, hev, hl⟩ |
    ⟨src, term, l, pi, pt, es, lc, hev, hl, _, _, _, hrole, _⟩ |
    ⟨src, term, lid, lastIdx, anchor, pairs, hev, _, _, hrole, _⟩
  · exact hl
  · exfalso
    subst hev
    have hlead : s.role = Role.leader := by
      rcases Classical.em (s.role = Role.leader) with hc | hc
      · exact hc
      · exfalso
        rw [Protocol.step, handleClientReq, if_pos (by simp [hc])] at hl
        have := congrArg LogStore.lastIndex hl
        simp only [LogStore.lastIndex_append] at this
        omega
    have : (Protocol.step s (Event.clientReq rid cmd)).1.role = Role.leader := by
      rw [Protocol.step, handleClientReq, if_neg (by rw [hlead]; simp)]
      dsimp only; simp [hlead]
    rw [this] at h; exact Role.noConfusion h
  · exfalso
    -- replication always demotes the receiver to follower
    rw [hrole] at h; exact Role.noConfusion h
  · exfalso
    -- and so does a snapshot
    rw [hrole] at h; exact Role.noConfusion h

/-- **Becoming a candidate strictly advances the term.** -/
theorem candidate_term_grows {s : NodeState σ κ} {ev : Event}
    (h : (Protocol.step s ev).1.role = Role.candidate) (hne : s.role ≠ Role.candidate) :
    s.currentTerm < (Protocol.step s ev).1.currentTerm := by
  rcases step_votes_char (by rw [h]; exact fun hc => Role.noConfusion hc) with
    ⟨hev, _, _⟩ | ⟨hold, hterm, _⟩
  · subst hev
    rw [Protocol.step] at h ⊢
    by_cases hlead : s.role == Role.leader
    · exfalso
      rw [if_pos hlead] at h
      rw [(by simpa using hlead : s.role = Role.leader)] at h
      exact Role.noConfusion h
    · rw [if_neg hlead] at h ⊢
      rw [startElection_term]; omega
  · exfalso
    -- the node was already campaigning or leading; leading cannot turn into candidacy
    rcases Classical.em (s.role = Role.leader) with hlead | hlead
    · exact leader_not_to_candidate hlead h
    · cases hq : s.role with
      | follower => exact hold hq
      | candidate => exact hne hq
      | leader => exact hlead hq

/-- Assuming leadership without a term change means the node was campaigning. -/
theorem leader_from_candidate {s : NodeState σ κ} {ev : Event}
    (hpost : (Protocol.step s ev).1.role = Role.leader) (hpre : s.role ≠ Role.leader)
    (hterm : (Protocol.step s ev).1.currentTerm = s.currentTerm) :
    s.role = Role.candidate := by
  rcases step_votes_char (by rw [hpost]; exact fun hc => Role.noConfusion hc) with
    ⟨hev, _, _⟩ | ⟨hold, _, _⟩
  · exfalso
    subst hev
    rw [Protocol.step] at hpost hterm
    by_cases hlead : s.role == Role.leader
    · exact hpre (by simpa using hlead)
    · rw [if_neg hlead] at hterm
      rw [startElection_term] at hterm; omega
  · cases hq : s.role with
    | follower => exact absurd hq hold
    | candidate => rfl
    | leader => exact absurd hq hpre

/-- Assuming leadership does not move the log. -/
theorem leader_log_unchanged {s : NodeState σ κ} {ev : Event}
    (hpost : (Protocol.step s ev).1.role = Role.leader) (hpre : s.role ≠ Role.leader) :
    (Protocol.step s ev).1.log = s.log := by
  rcases step_log s ev with hl | ⟨rid, cmd, hev, hl⟩ |
    ⟨src, term, l, pi, pt, es, lc, hev, hl, _, _, _, hrole, _⟩ |
    ⟨src, term, lid, lastIdx, anchor, pairs, hev, _, _, hrole, _⟩
  · exact hl
  · exfalso
    subst hev
    refine hpre ?_
    rcases Classical.em (s.role = Role.leader) with hc | hc
    · exact hc
    · exfalso
      rw [Protocol.step, handleClientReq, if_pos (by simp [hc])] at hl
      have := congrArg LogStore.lastIndex hl
      simp only [LogStore.lastIndex_append] at this
      omega
  · exfalso; rw [hrole] at hpost; exact Role.noConfusion hpost
  · exfalso; rw [hrole] at hpost; exact Role.noConfusion hpost

/-- The same for the logical log: becoming leader touches neither. -/
theorem leader_full_unchanged {w : World σ κ} {i : Nat} {ev : Event}
    (hpost : (Protocol.step (w.nodes i) ev).1.role = Role.leader)
    (hpre : (w.nodes i).role ≠ Role.leader) :
    fullStep w i ev = w.full i := by
  rcases world_full_step w i ev with hl | ⟨rid, cmd, hev, hlead, hl⟩ |
    ⟨src, term, l, pi, pt, es, lc, hev, ha, hl⟩ |
    ⟨src, term, lid, lastIdx, anchor, pairs, hev, hi, hct⟩
  · exact hl
  · exact absurd hlead hpre
  · exfalso
    subst hev
    have hct := aeAccepts_term ha
    rw [Protocol.step, handleAppendEntries, if_neg (by omega)] at hpost
    dsimp only at hpost
    split at hpost <;> simp at hpost
  · exfalso
    subst hev
    have hlt : ¬ (term < (w.nodes i).currentTerm) := by omega
    rw [Protocol.step, handleInstallSnapshot_follower _ _ _ _ _ _ hlt] at hpost
    exact Role.noConfusion hpost

/-! ## The advertised log is the real one -/

/-- A `requestVote`'s term never exceeds its sender's current term. -/
def RVTermBound (w : World σ κ) : Prop :=
  ∀ c d U cid li lt, (c, d, Msg.requestVote U cid li lt) ∈ w.sent →
    U ≤ (w.nodes c).currentTerm

/--
**While a node is still campaigning in the term it advertised, the advertised
`lastIndex`/`lastTerm` really are its own.**
-/
def CandLog (w : World σ κ) : Prop :=
  ∀ c d U cid li lt, (c, d, Msg.requestVote U cid li lt) ∈ w.sent →
    (w.nodes c).currentTerm = U → (w.nodes c).role = Role.candidate →
    li = LogStore.lastIndex (w.nodes c).log ∧ lt = LogStore.lastTerm (w.nodes c).log

/-- The candidate-advertisement invariants. -/
structure CandInv (members : List Nat) (w : World σ κ) : Prop where
  /-- Advertised terms are in the past. -/
  bound : RVTermBound w
  /-- Advertisements match the candidate's log. -/
  log : CandLog w

theorem candInv_init (members : List Nat) :
    CandInv (σ := σ) (κ := κ) members (World.init members) where
  bound := by intro c d U cid li lt h; simp [World.init] at h
  log := by intro c d U cid li lt h; simp [World.init] at h

/-- **The candidate-advertisement invariants are preserved by every step.** -/
theorem candInv_step {members : List Nat} {w w' : World σ κ}
    (h : CandInv members w) (hs : Step members w w') : CandInv members w' := by
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev → CandInv members w' := by
    intro j ev hw
    subst hw
    -- what a fresh advertisement says about the sender's post-state
    have fresh : ∀ c d U cid li lt, (c, d, Msg.requestVote U cid li lt)
        ∈ sendsOf j (Protocol.step (w.nodes j) ev).2 →
        c = j ∧ li = LogStore.lastIndex ((w.act j ev).nodes j).log
          ∧ lt = LogStore.lastTerm ((w.act j ev).nodes j).log
          ∧ ((w.act j ev).nodes j).currentTerm = U := by
      intro c d U cid li lt hp
      rcases mem_sendsOf hp with ⟨to, m, heq, hact⟩
      have hcj : c = j := congrArg (fun q => q.1) heq
      have hm : m = Msg.requestVote U cid li lt := by
        have := congrArg (fun q => q.2.2) heq; simpa using this.symm
      subst hm
      obtain ⟨h1, h2, h3, h4, _, _⟩ := step_requestVote_log hact
      refine ⟨hcj, ?_, ?_, ?_⟩
      · rw [act_nodes_self, h4]; exact h1
      · rw [act_nodes_self, h4]; exact h2
      · rw [act_nodes_self]; exact h3
    constructor
    · intro c d U cid li lt hp
      rw [act_sent] at hp
      rcases List.mem_append.mp hp with hp' | hp'
      · exact Nat.le_trans (h.bound c d U cid li lt hp') (act_term_mono w j ev c)
      · obtain ⟨hcj, _, _, ht⟩ := fresh c d U cid li lt hp'
        subst hcj
        exact Nat.le_of_eq ht.symm
    · intro c d U cid li lt hp hterm hrole
      rw [act_sent] at hp
      rcases List.mem_append.mp hp with hp' | hp'
      · by_cases hcj : c = j
        · subst hcj
          rw [act_nodes_self] at hterm hrole ⊢
          -- the term did not move, so the node was already a candidate at `U`
          have hb := h.bound c d U cid li lt hp'
          have hmono := act_term_mono w c ev c
          rw [act_nodes_self] at hmono
          have hold : (w.nodes c).currentTerm = U := by omega
          have holdrole : (w.nodes c).role = Role.candidate := by
            rcases Classical.em ((w.nodes c).role = Role.candidate) with hq | hq
            · exact hq
            · exfalso
              have := candidate_term_grows hrole hq
              omega
          obtain ⟨h1, h2⟩ := h.log c d U cid li lt hp' hold holdrole
          rw [candidate_log_stable hrole]
          exact ⟨h1, h2⟩
        · rw [act_nodes_ne _ _ _ hcj] at hterm hrole ⊢
          exact h.log c d U cid li lt hp' hterm hrole
      · obtain ⟨hcj, h1, h2, _⟩ := fresh c d U cid li lt hp'
        subst hcj
        exact ⟨h1, h2⟩
  cases hs with
  | deliver s d m hd hm => exact key d _ rfl
  | electionTimeout k hk => exact key k _ rfl
  | heartbeat k hk => exact key k _ rfl
  | client k rid cmd hk => exact key k _ rfl
  | crash k hk =>
      -- a restart comes back a follower, so the advertisement claim is vacuous at `k`
      refine ⟨?_, ?_⟩
      · intro c d U cid li lt hp
        rw [crash_sent] at hp
        by_cases hck : c = k
        · subst hck; rw [crash_nodes_self, restart_currentTerm]; exact h.bound c d U cid li lt hp
        · rw [crash_nodes_ne _ _ hck]; exact h.bound c d U cid li lt hp
      · intro c d U cid li lt hp hterm hrole
        rw [crash_sent] at hp
        by_cases hck : c = k
        · subst hck; rw [crash_nodes_self, restart_role] at hrole; exact absurd hrole (by simp)
        · rw [crash_nodes_ne _ _ hck] at hterm hrole ⊢
          exact h.log c d U cid li lt hp hterm hrole
  | compact k hk =>
      -- compaction changes neither the advertised log's extent nor the role
      refine ⟨?_, ?_⟩
      · intro c d U cid li lt hp
        rw [compactAt_sent] at hp
        by_cases hck : c = k
        · subst hck
          rw [compactAt_nodes_self, compactTo_currentTerm]
          exact h.bound c d U cid li lt hp
        · rw [compactAt_nodes_ne _ _ hck]; exact h.bound c d U cid li lt hp
      · intro c d U cid li lt hp hterm hrole
        rw [compactAt_sent] at hp
        by_cases hck : c = k
        · subst hck
          rw [compactAt_nodes_self, compactTo_currentTerm] at hterm
          rw [compactAt_nodes_self, compactTo_role] at hrole
          rw [compactAt_nodes_self]
          obtain ⟨e1, e2⟩ := h.log c d U cid li lt hp hterm hrole
          refine ⟨?_, ?_⟩
          · rw [e1, Protocol.compactTo]
            split
            · rename_i hg
              exact (LogStore.lastIndex_compact _ _ hg.2.1 hg.2.2).symm
            · rfl
          · rw [e2, Protocol.compactTo]
            split
            · rename_i hg
              unfold LogStore.lastTerm LogStore.termAt
              rw [LogStore.lastIndex_compact _ _ hg.2.1 hg.2.2]
              show _ = (Option.map Entry.term (LogStore.get
                (LogStore.compact (w.nodes c).log ((w.nodes c).lastApplied))
                (LogStore.lastIndex (w.nodes c).log))).getD 0
              rw [LogStore.get_compact_of_le _ _ _ hg.2.1 hg.2.2 (by omega)]
            · rfl
        · rw [compactAt_nodes_ne _ _ hck] at hterm hrole ⊢
          exact h.log c d U cid li lt hp hterm hrole

/-- The candidate-advertisement invariants hold in every reachable world. -/
theorem candInv_reachable {members : List Nat} {w : World σ κ} (h : Reachable members w) :
    CandInv members w := by
  induction h with
  | init => exact candInv_init members
  | tail _ hs ih => exact candInv_step ih hs

/--
**The log a leader was elected with is exactly the log it advertised.**

Joining `CandLog` to the election record: a node that assumes leadership without
a term change was a candidate an instant earlier, its log did not move in
between, and while campaigning its advertisement matched its log.
-/
def RVElected (w : World σ κ) : Prop :=
  ∀ c d U cid li lt (lg : σ), (c, d, Msg.requestVote U cid li lt) ∈ w.sent →
    (c, U, lg) ∈ w.elected →
    li = LogStore.lastIndex lg ∧ lt = LogStore.lastTerm lg

theorem rvElected_init (members : List Nat) :
    RVElected (σ := σ) (κ := κ) (World.init members) := by
  intro c d U cid li lt lg h; simp [World.init] at h

theorem rvElected_step {members : List Nat} {w w' : World σ κ}
    (hnd : members.Nodup) (hr : Reachable members w)
    (h : RVElected w) (hs : Step members w w') : RVElected w' := by
  have hc := candInv_reachable hr
  have hl := ledInv_reachable hnd hr
  have he := eInv_reachable hnd hr
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev → RVElected w' := by
    intro j ev hw
    subst hw
    intro c d U cid li lt lg hp hel
    rw [act_sent] at hp
    rw [act_elected] at hel
    rcases List.mem_append.mp hp with hp' | hp' <;>
      rcases List.mem_append.mp hel with hel' | hel'
    · exact h c d U cid li lt lg hp' hel'
    · -- an old advertisement meeting a fresh election record
      obtain ⟨h1, h2, h3, h4, h5⟩ := mem_electedOf hel'
      subst h1; subst h2; subst h3
      have hb := hc.bound c d _ cid li lt hp'
      have hmono := step_term_mono (w.nodes c) ev
      have hpre : (w.nodes c).currentTerm = (Protocol.step (w.nodes c) ev).1.currentTerm := by
        omega
      have hcand : (w.nodes c).role = Role.candidate :=
        leader_from_candidate h4 h5 hpre.symm
      obtain ⟨e1, e2⟩ := hc.log c d _ cid li lt hp' hpre hcand
      rw [leader_full_unchanged h4 h5]
      exact ⟨by rw [e1, full_lastIndex hr c], by rw [e2, full_lastTerm hr c]⟩
    · -- a fresh advertisement cannot meet an older election record for the same term
      exfalso
      rcases mem_sendsOf hp' with ⟨to, m, heq, hact⟩
      have hcj : c = j := congrArg (fun q => q.1) heq
      have hm : m = Msg.requestVote U cid li lt := by
        have := congrArg (fun q => q.2.2) heq; simpa using this.symm
      subst hm; subst hcj
      obtain ⟨_, _, ht, hlog, _, hgrow⟩ := step_requestVote_log hact
      have hled : (c, U) ∈ w.led := he.led c U lg hel'
      have hbound := hl.bound c U hled
      omega
    · -- both fresh: a campaigning node is not simultaneously assuming leadership
      exfalso
      rcases mem_sendsOf hp' with ⟨to, m, heq, hact⟩
      have hm : m = Msg.requestVote U cid li lt := by
        have := congrArg (fun q => q.2.2) heq; simpa using this.symm
      subst hm
      obtain ⟨_, _, _, _, hcand, _⟩ := step_requestVote_log hact
      obtain ⟨_, _, _, hlead, _⟩ := mem_electedOf hel'
      rw [hcand] at hlead; exact Role.noConfusion hlead
  cases hs with
  | deliver s d m hd hm => exact key d _ rfl
  | electionTimeout k hk => exact key k _ rfl
  | heartbeat k hk => exact key k _ rfl
  | client k rid cmd hk => exact key k _ rfl
  | crash k hk =>
      intro c d U cid li lt lg hp hel
      rw [crash_sent] at hp; rw [crash_elected] at hel
      exact h c d U cid li lt lg hp hel
  | compact k hk =>
      intro c d U cid li lt lg hp hel
      rw [compactAt_sent] at hp; rw [compactAt_elected] at hel
      exact h c d U cid li lt lg hp hel

/-- `RVElected` holds in every reachable world. -/
theorem rvElected_reachable {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) : RVElected w := by
  induction h with
  | init => exact rvElected_init members
  | tail hr hs ih => exact rvElected_step hnd hr ih hs

end RaftKV.Proof
