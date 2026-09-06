import RaftKV.Proof.Refine

/-!
# Linearizability

The top of the refinement chain. `stateMachineSafety` and `replicas_agree` say
the replicas agree with each other and with the sequential specification; this
file says the same thing about the *client-visible history*: every answer the
cluster ever gave is the answer a single, sequential key/value store would have
given, at a definite point in one global order, and that order never contradicts
real time.

The history lives in the ghost field `World.hist`, stamped with `World.clock` —
the number of steps taken. Because the model is an interleaving semantics, step
order *is* real-time order, so "A's response happened before B's invocation" is
exactly `respond`'s stamp being strictly less than `invoke`'s.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [LawfulLogStore σ] [KVStore κ]

/-! ## Ghost accessors -/

@[simp] theorem act_commits (w : World σ κ) (j : Nat) (ev : Event) :
    (w.act j ev).commits
      = w.commits ++ commitOf j (w.nodes j) (Protocol.step (w.nodes j) ev).1
          (fullStep (w.nodes j) (w.full j) ev) := rfl

@[simp] theorem act_created' (w : World σ κ) (j : Nat) (ev : Event) :
    (w.act j ev).created
      = w.created ++ createdOf j (Protocol.step (w.nodes j) ev).1 (fullStep (w.nodes j) (w.full j) ev) ev := rfl

@[simp] theorem act_hist (w : World σ κ) (j : Nat) (ev : Event) :
    (w.act j ev).hist
      = w.hist ++ histOf j ev (Protocol.step (w.nodes j) ev).2 w.clock := rfl

@[simp] theorem act_clock (w : World σ κ) (j : Nat) (ev : Event) :
    (w.act j ev).clock = w.clock + 1 := rfl

@[simp] theorem act_createTime (w : World σ κ) (j : Nat) (ev : Event) :
    (w.act j ev).createTime
      = w.createTime ++ createTimeOf j (Protocol.step (w.nodes j) ev).1 (fullStep (w.nodes j) (w.full j) ev) ev w.clock := rfl

@[simp] theorem act_commitTime (w : World σ κ) (j : Nat) (ev : Event) :
    (w.act j ev).commitTime
      = w.commitTime ++ commitTimeOf j (w.nodes j) (Protocol.step (w.nodes j) ev).1 (fullStep (w.nodes j) (w.full j) ev) w.clock := rfl

/-! ## Replies come only from applying committed entries -/

theorem stepDown_no_reply {s : NodeState σ κ} {t : Nat} {hint : Option Nat}
    {n rid : Nat} {r : Reply} : Action.reply n rid r ∉ (stepDown s t hint).2 := by
  rw [stepDown]
  intro h
  rcases List.mem_map.mp h with ⟨p, _, hq⟩
  exact Action.noConfusion hq

theorem maybeStepDown_no_reply {s : NodeState σ κ} {t : Nat} {hint : Option Nat}
    {n rid : Nat} {r : Reply} : Action.reply n rid r ∉ (maybeStepDown s t hint).2 := by
  rw [maybeStepDown]; split
  · exact stepDown_no_reply
  · simp

theorem broadcastAppend_no_reply {s : NodeState σ κ} {n rid : Nat} {r : Reply} :
    Action.reply n rid r ∉ broadcastAppend s := by
  rw [broadcastAppend]
  intro h
  rcases List.mem_map.mp h with ⟨p, _, hq⟩
  exact Action.noConfusion hq

theorem startElection_no_reply {s : NodeState σ κ} {n rid : Nat} {r : Reply} :
    Action.reply n rid r ∉ (startElection s).2 := by
  rw [startElection]
  split
  · rw [becomeLeader]; exact broadcastAppend_no_reply
  · dsimp only
    intro h
    rcases List.mem_map.mp h with ⟨p, _, hq⟩
    exact Action.noConfusion hq

/--
**Every client reply is produced by draining the commit queue**, against a state
whose log and commit index are the step's own, and whose key/value state and
`lastApplied` are the ones the step started from.
-/
theorem reply_from_applyCommitted {s : NodeState σ κ} {ev : Event} {n rid : Nat} {r : Reply}
    (h : Action.reply n rid r ∈ (Protocol.step s ev).2) :
    ∃ s₀ : NodeState σ κ, (Protocol.step s ev).1 = (applyCommitted s₀).1
      ∧ s₀.kv = s.kv ∧ s₀.lastApplied = s.lastApplied
      ∧ Action.reply n rid r ∈ (applyCommitted s₀).2 := by
  cases ev with
  | recv src m =>
      cases m with
      | requestVote term c li lt =>
          exfalso
          rw [Protocol.step, handleRequestVote] at h
          split at h
          · rcases List.mem_singleton.mp h with hq; exact Action.noConfusion hq
          · dsimp only at h
            split at h <;>
              (rcases List.mem_append.mp h with h' | h'
               · exact maybeStepDown_no_reply h'
               · rcases List.mem_singleton.mp h' with hq; exact Action.noConfusion hq)
      | requestVoteResp term g =>
          exfalso
          rw [Protocol.step, handleRequestVoteResp] at h
          split at h
          · exact stepDown_no_reply h
          · split at h
            · simp at h
            · dsimp only at h
              split at h <;> split at h <;>
                (first
                  | (rw [becomeLeader] at h; exact broadcastAppend_no_reply h)
                  | simp at h)
      | appendEntries term l pi pt es lc =>
          rw [Protocol.step, handleAppendEntries] at h ⊢
          split at h
          · exfalso; rcases List.mem_singleton.mp h with hq; exact Action.noConfusion hq
          · rename_i hlt
            rw [if_neg hlt]
            dsimp only at h ⊢
            split at h
            · exfalso
              rcases List.mem_append.mp h with h' | h'
              · exact maybeStepDown_no_reply h'
              · rcases List.mem_singleton.mp h' with hq; exact Action.noConfusion hq
            · rename_i hc
              rw [if_neg hc]
              dsimp only
              refine ⟨_, rfl, by simp, by simp, ?_⟩
              rcases List.mem_append.mp h with h' | h'
              · exact absurd h' maybeStepDown_no_reply
              · rcases List.mem_cons.mp h' with hq | hq
                · exact absurd hq (by simp)
                · exact hq
      | appendEntriesResp term ok mi =>
          rw [Protocol.step, handleAppendEntriesResp] at h ⊢
          split at h
          · exact absurd h stepDown_no_reply
          · rename_i h1
            rw [if_neg h1]
            split at h
            · simp at h
            · rename_i h2
              rw [if_neg h2]
              split at h
              · rename_i h3
                rw [if_pos h3]
                dsimp only
                exact ⟨_, rfl, by simp, by simp, h⟩
              · exfalso; rcases List.mem_singleton.mp h with hq; exact Action.noConfusion hq
  | clientReq rid' cmd =>
      rw [Protocol.step, handleClientReq] at h ⊢
      split at h
      · exfalso; rcases List.mem_singleton.mp h with hq; exact Action.noConfusion hq
      · rename_i hg
        rw [if_neg hg]
        dsimp only at h ⊢
        refine ⟨_, rfl, by simp, by simp, ?_⟩
        rcases List.mem_append.mp h with h' | h'
        · exact absurd h' broadcastAppend_no_reply
        · exact h'
  | electionTimeout =>
      exfalso
      rw [Protocol.step] at h
      split at h
      · simp at h
      · exact startElection_no_reply h
  | heartbeatTimeout =>
      exfalso
      rw [Protocol.step] at h
      split at h
      · exact broadcastAppend_no_reply h
      · simp at h


/-! ## The reply a client gets is the specification's answer -/

section Lawful

variable [LawfulKVStore κ]

/--
**Every reply the apply-loop emits is the sequential specification's answer**,
computed on the commands at indices `1 … n-1`, for the command at `n`.
-/
theorem applyLoop_reply (fl : σ) (f : Nat) (s : NodeState σ κ) (acc : List Action)
    (hbr : ∀ k, LogStore.firstIndex s.log ≤ k → LogStore.get s.log k = LogStore.get fl k)
    (hfa : LogStore.firstIndex s.log ≤ s.lastApplied + 1)
    (hmod : AppliedModel fl s) {n rid : Nat} {r : Reply}
    (h : Action.reply n rid r ∈ (applyLoop f s acc).2) :
    Action.reply n rid r ∈ acc
      ∨ (∃ e, LogStore.get fl n = some e ∧ e.reqId = rid
          ∧ 1 ≤ n ∧ n ≤ s.commitIndex
          ∧ r = (Spec.applyCmd (Spec.run (cmdsUpTo fl (n - 1))) e.cmd).2) := by
  induction f generalizing s acc with
  | zero => rw [applyLoop] at h; exact Or.inl h
  | succ f ih =>
      rw [applyLoop] at h
      split at h
      · rename_i hlt
        have hlog0 : (applyOne s).1.log = s.log := applyOne_log s
        have hla0 : s.lastApplied ≤ (applyOne s).1.lastApplied := applyOne_lastApplied_ge s
        rcases ih (applyOne s).1 (acc ++ (applyOne s).2)
          (fun k hk => by rw [hlog0] at hk ⊢; exact hbr k hk)
          (by rw [hlog0]; omega)
          (applyOne_refines fl s hbr hfa hmod) h with h' | h'
        · rcases List.mem_append.mp h' with h'' | h''
          · exact Or.inl h''
          · -- this very entry was just applied
            right
            revert h''
            show Action.reply n rid r ∈ (applyOne s).2 → _
            rw [applyOne]
            cases hq : LogStore.get s.log (s.lastApplied + 1) with
            | none => intro hz; simp at hz
            | some e =>
                dsimp only
                cases hkv : KVStore.applyCmd s.kv e.cmd with
                | mk kv' rep =>
                    dsimp only
                    split
                    · intro hz
                      have hz' := List.mem_singleton.mp hz
                      have h1 : n = s.lastApplied + 1 := (Action.reply.inj hz').1
                      have h2 : rid = e.reqId := (Action.reply.inj hz').2.1
                      have h3 : r = rep := (Action.reply.inj hz').2.2
                      refine ⟨e, by rw [h1, ← hbr _ hfa]; exact hq, h2.symm, by omega,
                        by omega, ?_⟩
                      have hrep : rep = (Spec.applyCmd (LawfulKVStore.toModel s.kv) e.cmd).2 := by
                        have := KVStore.applyCmd_reply s.kv e.cmd
                        rw [hkv] at this; exact this
                      unfold AppliedModel at hmod
                      rw [h3, hrep, hmod, h1]
                      simp
                    · intro hz; simp at hz
        · right
          obtain ⟨e, he1, he2, he3, he4, he5⟩ := h'
          have hci : (applyOne s).1.commitIndex = s.commitIndex := applyOne_commitIndex s
          rw [hci] at he4
          exact ⟨e, he1, he2, he3, he4, he5⟩
      · exact Or.inl h

theorem applyCommitted_reply (fl : σ) (s : NodeState σ κ)
    (hbr : ∀ k, LogStore.firstIndex s.log ≤ k → LogStore.get s.log k = LogStore.get fl k)
    (hfa : LogStore.firstIndex s.log ≤ s.lastApplied + 1)
    (hmod : AppliedModel fl s)
    {n rid : Nat} {r : Reply} (h : Action.reply n rid r ∈ (applyCommitted s).2) :
    ∃ e, LogStore.get fl n = some e ∧ e.reqId = rid
      ∧ 1 ≤ n ∧ n ≤ s.commitIndex
      ∧ r = (Spec.applyCmd (Spec.run (cmdsUpTo fl (n - 1))) e.cmd).2 := by
  rcases applyLoop_reply fl _ s [] hbr hfa hmod h with h' | h'
  · simp at h'
  · exact h'

/--
**Every reply a step emits is the specification's answer at a committed index.**
-/
theorem step_reply (fl : σ) (s : NodeState σ κ) (ev : Event)
    (hbr : ∀ k, LogStore.firstIndex (Protocol.step s ev).1.log ≤ k →
      LogStore.get (Protocol.step s ev).1.log k = LogStore.get fl k)
    (hfa : LogStore.firstIndex s.log ≤ s.lastApplied + 1)
    (hpre : AppliedModel fl s)
    {n rid : Nat} {r : Reply} (h : Action.reply n rid r ∈ (Protocol.step s ev).2) :
    ∃ e, LogStore.get fl n = some e ∧ e.reqId = rid
      ∧ 1 ≤ n ∧ n ≤ (Protocol.step s ev).1.commitIndex
      ∧ r = (Spec.applyCmd (Spec.run (cmdsUpTo fl (n - 1))) e.cmd).2 := by
  obtain ⟨s₀, hpost, hkv, hla, hmem⟩ := reply_from_applyCommitted h
  have hlog : (Protocol.step s ev).1.log = s₀.log := by rw [hpost]; simp
  have hci : (Protocol.step s ev).1.commitIndex = s₀.commitIndex := by rw [hpost]; simp
  have hmod : AppliedModel fl s₀ := by
    unfold AppliedModel at hpre ⊢
    rw [hkv, hla]
    exact hpre
  obtain ⟨e, h1, h2, h3, h4, h5⟩ := applyCommitted_reply fl s₀
    (fun k hk => by rw [← hlog] at hk ⊢; exact hbr k hk)
    (by rw [hla, ← hlog, step_firstIndex]; exact hfa)
    hmod hmem
  exact ⟨e, h1, h2, h3, by rw [hci]; exact h4, h5⟩

end Lawful


/-! ## Membership in the new ghost records -/

/-- The response half of a step's history is exactly its `reply` actions. -/
theorem mem_replyMap {i t : Nat} {acts : List Action} {t' i' rid n : Nat} {r : Reply}
    (h : HEvent.respond t' i' rid n r ∈ acts.filterMap (fun a =>
        match a with
        | .reply idx rid r => some (HEvent.respond t i rid idx r)
        | _ => none)) :
    t' = t ∧ i' = i ∧ Action.reply n rid r ∈ acts := by
  rcases List.mem_filterMap.mp h with ⟨a, ha, heq⟩
  cases a with
  | send _ _ => simp at heq
  | notLeader _ _ => simp at heq
  | reply idx rid₂ r₂ =>
      simp only [Option.some.injEq] at heq
      obtain ⟨e1, e2, e3, e4, e5⟩ := HEvent.respond.inj heq
      rw [e3, e4, e5] at ha
      exact ⟨e1.symm, e2.symm, ha⟩

/-- No invocation ever comes out of a `reply` action. -/
theorem not_mem_replyMap {i t : Nat} {acts : List Action} {t' i' rid : Nat} {cmd : Command} :
    HEvent.invoke t' i' rid cmd ∉ acts.filterMap (fun a =>
        match a with
        | .reply idx rid r => some (HEvent.respond t i rid idx r)
        | _ => none) := by
  intro h
  rcases List.mem_filterMap.mp h with ⟨a, _, heq⟩
  cases a with
  | send _ _ => simp at heq
  | notLeader _ _ => simp at heq
  | reply _ _ _ => simp only [Option.some.injEq] at heq; exact HEvent.noConfusion heq

theorem mem_histOf_respond {i t : Nat} {ev : Event} {acts : List Action}
    {t' i' rid n : Nat} {r : Reply}
    (h : HEvent.respond t' i' rid n r ∈ histOf i ev acts t) :
    t' = t ∧ i' = i ∧ Action.reply n rid r ∈ acts := by
  cases ev with
  | clientReq a b =>
      rw [histOf] at h
      rcases List.mem_append.mp h with h' | h'
      · exact absurd (List.mem_singleton.mp h') (by simp)
      · exact mem_replyMap h'
  | recv a b =>
      rw [histOf] at h
      rcases List.mem_append.mp h with h' | h'
      · exact absurd h' (by simp)
      · exact mem_replyMap h'
  | electionTimeout =>
      rw [histOf] at h
      rcases List.mem_append.mp h with h' | h'
      · exact absurd h' (by simp)
      · exact mem_replyMap h'
  | heartbeatTimeout =>
      rw [histOf] at h
      rcases List.mem_append.mp h with h' | h'
      · exact absurd h' (by simp)
      · exact mem_replyMap h'

theorem mem_histOf_invoke {i t : Nat} {ev : Event} {acts : List Action}
    {t' i' rid : Nat} {cmd : Command}
    (h : HEvent.invoke t' i' rid cmd ∈ histOf i ev acts t) :
    t' = t ∧ i' = i ∧ ev = Event.clientReq rid cmd := by
  cases ev with
  | clientReq a b =>
      rw [histOf] at h
      rcases List.mem_append.mp h with h' | h'
      · obtain ⟨e1, e2, e3, e4⟩ := HEvent.invoke.inj (List.mem_singleton.mp h')
        exact ⟨e1, e2, by rw [e3, e4]⟩
      · exact absurd h' not_mem_replyMap
  | recv a b =>
      rw [histOf] at h
      rcases List.mem_append.mp h with h' | h'
      · exact absurd h' (by simp)
      · exact absurd h' not_mem_replyMap
  | electionTimeout =>
      rw [histOf] at h
      rcases List.mem_append.mp h with h' | h'
      · exact absurd h' (by simp)
      · exact absurd h' not_mem_replyMap
  | heartbeatTimeout =>
      rw [histOf] at h
      rcases List.mem_append.mp h with h' | h'
      · exact absurd h' (by simp)
      · exact absurd h' not_mem_replyMap

theorem mem_createTimeOf {i t : Nat} {s : NodeState σ κ} {fl : σ} {ev : Event}
    {e : Entry} {t' : Nat}
    (h : (e, t') ∈ createTimeOf i s fl ev t) :
    t' = t ∧ ∃ c k, (c, k, e) ∈ createdOf i s fl ev := by
  rcases List.mem_map.mp h with ⟨r, hr, heq⟩
  have h1 : r.2.2 = e := congrArg (fun p => p.1) heq
  have h2 : t = t' := congrArg (fun p => p.2) heq
  exact ⟨h2.symm, r.1, r.2.1, by rw [← h1]; exact hr⟩

theorem mem_commitTimeOf {i t : Nat} {pre post : NodeState σ κ} {c : Nat} {lg fl : σ} {t' : Nat}
    (h : (c, lg, t') ∈ commitTimeOf i pre post fl t) :
    t' = t ∧ ∃ L T Q, (L, T, c, lg, Q) ∈ commitOf i pre post fl := by
  rcases List.mem_map.mp h with ⟨r, hr, heq⟩
  have h1 : r.2.2.1 = c := congrArg (fun p => p.1) heq
  have h2 : r.2.2.2.1 = lg := congrArg (fun p => p.2.1) heq
  have h3 : t = t' := congrArg (fun p => p.2.2) heq
  exact ⟨h3.symm, r.1, r.2.1, r.2.2.2.2, by rw [← h1, ← h2]; exact hr⟩

/-! ## Committed prefixes of two logs agree -/

/-- A commit record's log holds a committed entry at every index up to its own. -/
theorem commit_covers {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w)
    {L T c : Nat} {lg : σ} {Q : List Nat} (hc : (L, T, c, lg, Q) ∈ w.commits)
    {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ c) :
    ∃ e, LogStore.get lg k = some e ∧ Protocol.Committed w k e T := by
  obtain ⟨hcT, _⟩ := commit_ack_quorum hnd hrch hc
  have hlen : c ≤ LogStore.lastIndex lg := by
    unfold LogStore.termAt at hcT
    cases hq : LogStore.get lg c with
    | none => rw [hq] at hcT; simp at hcT
    | some z => exact ((LogStore.get_isSome_iff lg c).mp (by rw [hq]; rfl)).2
  obtain ⟨e, he⟩ : ∃ e, LogStore.get lg k = some e := by
    cases hq : LogStore.get lg k with
    | none =>
        exfalso
        have hnc : LogStore.firstIndex lg = 1 :=
          ((snapWF_reachable hnd hrch).1 L T c lg Q hc).nocompact
        have := (LogStore.get_isSome_iff lg k).mpr ⟨by omega, by omega⟩
        rw [hq] at this; exact Bool.noConfusion this
    | some e => exact ⟨e, rfl⟩
  exact ⟨e, he, L, c, lg, Q, hc, h2, he⟩

/-- Two logs that both hold the committed prefix up to `n` agree up to `n`. -/
theorem committed_prefix_agree {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) {lg₁ lg₂ : σ} {n : Nat}
    (h₁ : ∀ k, 1 ≤ k → k ≤ n → ∃ e T, LogStore.get lg₁ k = some e ∧ Protocol.Committed w k e T)
    (h₂ : ∀ k, 1 ≤ k → k ≤ n → ∃ e T, LogStore.get lg₂ k = some e ∧ Protocol.Committed w k e T) :
    ∀ k, k ≤ n → LogStore.get lg₁ k = LogStore.get lg₂ k := by
  intro k hk
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0; simp
  · obtain ⟨e₁, T₁, g₁, c₁⟩ := h₁ k h0 hk
    obtain ⟨e₂, T₂, g₂, c₂⟩ := h₂ k h0 hk
    rw [g₁, g₂, committed_unique hnd hrch c₁ c₂]


/-- A minted entry records the very request that was submitted. -/
theorem createdOf_event {i j k : Nat} {e : Entry} {s : NodeState σ κ} {fl : σ} {ev : Event}
    (h : (i, k, e) ∈ createdOf j s fl ev) : ev = Event.clientReq e.reqId e.cmd := by
  unfold createdOf at h
  cases ev with
  | clientReq rid cmd =>
      dsimp only at h
      split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        rw [h.2.2]
      · simp at h
  | recv a b => simp at h
  | electionTimeout => simp at h
  | heartbeatTimeout => simp at h

/-! ## The history invariants -/

section Hist

variable [LawfulKVStore κ]

/-- Every minted entry has a creation time, in the past. -/
def CreatedTime (w : World σ κ) : Prop :=
  ∀ c k (e : Entry), (c, k, e) ∈ w.created → ∃ t, (e, t) ∈ w.createTime ∧ t < w.clock

/-- Every commit has a commit time, in the past. -/
def CommitsTime (w : World σ κ) : Prop :=
  ∀ L T c (lg : σ) Q, (L, T, c, lg, Q) ∈ w.commits →
    ∃ t, (c, lg, t) ∈ w.commitTime ∧ t < w.clock

/-- Nothing is minted that a client did not ask for, at that very moment. -/
def CreateInvoke (w : World σ κ) : Prop :=
  ∀ (e : Entry) t, (e, t) ∈ w.createTime → ∃ i, HEvent.invoke t i e.reqId e.cmd ∈ w.hist

/-- Every commit time names a real commit. -/
def CommitTimeIsCommit (w : World σ κ) : Prop :=
  ∀ c (lg : σ) t, (c, lg, t) ∈ w.commitTime → ∃ L T Q, (L, T, c, lg, Q) ∈ w.commits

/-- Nothing is committed before it was minted. -/
def CommitCreate (w : World σ κ) : Prop :=
  ∀ c (lg : σ) t, (c, lg, t) ∈ w.commitTime → ∀ k (e : Entry), 1 ≤ k → k ≤ c →
    LogStore.get lg k = some e → ∃ t', (e, t') ∈ w.createTime ∧ t' ≤ t

/--
**Every response is the specification's answer at a committed index.**

The response for request `rid` at index `n` names a commit that had already
happened, whose log holds `rid`'s entry at `n`, and the reply is exactly what
the sequential specification returns for that command after the `n-1` commands
below it.
-/
def RespondCommitted (w : World σ κ) : Prop :=
  ∀ t i rid n r, HEvent.respond t i rid n r ∈ w.hist →
    ∃ (c : Nat) (lg : σ) (t' : Nat) (e : Entry),
      (c, lg, t') ∈ w.commitTime ∧ t' ≤ t ∧ 1 ≤ n ∧ n ≤ c
        ∧ LogStore.get lg n = some e ∧ e.reqId = rid
        ∧ r = (Spec.applyCmd (Spec.run (cmdsUpTo lg (n - 1))) e.cmd).2

/-- The history invariants, carried together. -/
structure LInv (members : List Nat) (w : World σ κ) : Prop where
  /-- Minted entries are stamped. -/
  createdTime : CreatedTime w
  /-- Commits are stamped. -/
  commitsTime : CommitsTime w
  /-- Commit times name real commits. -/
  commitTimeIsCommit : CommitTimeIsCommit w
  /-- Minting answers an invocation. -/
  createInvoke : CreateInvoke w
  /-- Committing follows minting. -/
  commitCreate : CommitCreate w
  /-- Responses are the specification's answers. -/
  respondCommitted : RespondCommitted w

theorem lInv_init (members : List Nat) : LInv (σ := σ) (κ := κ) members (World.init members) where
  createdTime := by intro c k e h; simp [World.init] at h
  commitsTime := by intro L T c lg Q h; simp [World.init] at h
  commitTimeIsCommit := by intro c lg t h; simp [World.init] at h
  createInvoke := by intro e t h; simp [World.init] at h
  commitCreate := by intro c lg t h; simp [World.init] at h
  respondCommitted := by intro t i rid n r h; simp [World.init] at h


/-- **The history invariants are preserved by every step.** -/
theorem lInv_step {members : List Nat} {w w' : World σ κ}
    (hnd : members.Nodup) (hr : Reachable members w)
    (h : LInv members w) (hs : Step members w w') : LInv members w' := by
  have hr' : Reachable members w' := Reachable.tail hr hs
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev →
      (∀ src m', ev = Event.recv src m' → (src, j, m') ∈ w.sent) → LInv members w' := by
    intro j ev hw hdel
    subst hw
    -- stamps first: they depend on nothing else
    have hct : CreatedTime (w.act j ev) := by
      intro c k e hmem
      rw [act_created] at hmem
      rw [act_createTime, act_clock]
      rcases List.mem_append.mp hmem with h' | h'
      · obtain ⟨t, h1, h2⟩ := h.createdTime c k e h'
        exact ⟨t, List.mem_append_left _ h1, by omega⟩
      · exact ⟨w.clock, List.mem_append_right _
          (List.mem_map.mpr ⟨(c, k, e), h', rfl⟩), by omega⟩
    have hmt : CommitsTime (w.act j ev) := by
      intro L T c lg Q hmem
      rw [act_commitTime, act_clock]
      rcases List.mem_append.mp hmem with h' | h'
      · obtain ⟨t, h1, h2⟩ := h.commitsTime L T c lg Q h'
        exact ⟨t, List.mem_append_left _ h1, by omega⟩
      · exact ⟨w.clock, List.mem_append_right _
          (List.mem_map.mpr ⟨(L, T, c, lg, Q), h', rfl⟩), by omega⟩
    have hti : CommitTimeIsCommit (w.act j ev) := by
      intro c lg t hmem
      rw [act_commits]
      rcases List.mem_append.mp hmem with h' | h'
      · obtain ⟨L, T, Q, hq⟩ := h.commitTimeIsCommit c lg t h'
        exact ⟨L, T, Q, List.mem_append_left _ hq⟩
      · obtain ⟨_, L, T, Q, hq⟩ := mem_commitTimeOf h'
        exact ⟨L, T, Q, List.mem_append_right _ hq⟩
    have hci : CreateInvoke (w.act j ev) := by
      intro e t hmem
      rw [act_createTime] at hmem
      rw [act_hist]
      rcases List.mem_append.mp hmem with h' | h'
      · obtain ⟨i, hi⟩ := h.createInvoke e t h'
        exact ⟨i, List.mem_append_left _ hi⟩
      · obtain ⟨ht, c, k, hcr⟩ := mem_createTimeOf h'
        subst ht
        refine ⟨j, List.mem_append_right _ ?_⟩
        rw [createdOf_event hcr, histOf]
        exact List.mem_append_left _ (by simp)
    have hcc : CommitCreate (w.act j ev) := by
      intro c lg t hmem k e hk1 hk2 hget
      rw [act_createTime]
      rcases List.mem_append.mp hmem with h' | h'
      · obtain ⟨t', h1, h2⟩ := h.commitCreate c lg t h' k e hk1 hk2 hget
        exact ⟨t', List.mem_append_left _ h1, h2⟩
      · obtain ⟨ht, L, T, Q, hcm⟩ := mem_commitTimeOf h'
        subst ht
        obtain ⟨_, _, _, hlg, _, _, _⟩ := mem_commitOf hcm
        have hnode : ((w.act j ev).full j) = lg := by
          rw [act_full_self]; exact hlg.symm
        obtain ⟨c₀, hc₀⟩ := (wf_node hnd hr' j).created k e (by rw [hnode]; exact hget)
        obtain ⟨t', h1, h2⟩ := hct c₀ k e hc₀
        rw [act_clock] at h2
        rw [act_createTime] at h1
        exact ⟨t', h1, by omega⟩
    refine ⟨hct, hmt, hti, hci, hcc, ?_⟩
    -- responses
    intro t i rid n r hmem
    rw [act_hist] at hmem
    rcases List.mem_append.mp hmem with h' | h'
    · obtain ⟨c, lg, t', e, h1, h2, h3, h4, h5, h6, h7⟩ := h.respondCommitted t i rid n r h'
      exact ⟨c, lg, t', e, List.mem_append_left _ h1, h2, h3, h4, h5, h6, h7⟩
    · obtain ⟨htt, hij, hact⟩ := mem_histOf_respond h'
      subst htt; subst hij
      obtain ⟨e, hg, hrid, hn1, hn2, hspec⟩ :=
        step_reply (fullStep (w.nodes i) (w.full i) ev) (w.nodes i) ev
          (fun k hk => by
            have := full_get hr' (i := i) (k := k) (by rw [act_nodes_self]; exact hk)
            rwa [act_nodes_self, act_full_self] at this)
          (full_applied hr i)
          (step_appliedModel_pre hnd hr hdel) hact
      -- the applied entry is committed
      have hnode : ((w.act i ev).nodes i) = (Protocol.step (w.nodes i) ev).1 := act_nodes_self w i ev
      have hfnode : ((w.act i ev).full i) = fullStep (w.nodes i) (w.full i) ev :=
        act_full_self w i ev
      obtain ⟨T, hcom, _⟩ := (sInv_reachable hnd hr').cov i n e
        (by rw [hnode]; exact hn2) (by rw [hfnode]; exact hg)
      obtain ⟨L, c, lgc, Q, hcm, hnc, hgc⟩ := hcom
      obtain ⟨t', ht1, ht2⟩ := hmt L T c lgc Q hcm
      rw [act_clock] at ht2
      refine ⟨c, lgc, t', e, ht1, by omega, hn1, hnc, hgc, hrid, ?_⟩
      -- the two logs hold the same committed prefix below `n`
      have hagree : ∀ k, k ≤ n - 1 →
          LogStore.get lgc k = LogStore.get (fullStep (w.nodes i) (w.full i) ev) k := by
        refine committed_prefix_agree hnd hr' ?_ ?_
        · intro k hk1 hk2
          obtain ⟨e', hg', hc'⟩ := commit_covers hnd hr' hcm hk1 (by omega)
          exact ⟨e', T, hg', hc'⟩
        · intro k hk1 hk2
          obtain ⟨e', hg'⟩ : ∃ e',
              LogStore.get (fullStep (w.nodes i) (w.full i) ev) k = some e' := by
            cases hq : LogStore.get (fullStep (w.nodes i) (w.full i) ev) k with
            | none =>
                exfalso
                have hb := (sInv_reachable hnd hr').bound i
                rw [hfnode, hnode] at hb
                have := (LogStore.get_isSome_iff
                  (fullStep (w.nodes i) (w.full i) ev) k).mpr
                  ⟨by rw [← hfnode, full_firstIndex hr' i]; omega, by omega⟩
                rw [hq] at this; exact Bool.noConfusion this
            | some e' => exact ⟨e', rfl⟩
          obtain ⟨T', hc', _⟩ := (sInv_reachable hnd hr').cov i k e'
            (by rw [hnode]; omega) (by rw [hfnode]; exact hg')
          exact ⟨e', T', hg', hc'⟩
      rw [hspec, cmdsUpTo_congr _ hagree]
  cases hs with
  | deliver s d m0 hd hmem =>
      refine key d _ rfl ?_
      intro src' m' heq
      have h1 : s = src' := (Event.recv.inj heq).1
      have h2 : m0 = m' := (Event.recv.inj heq).2
      subst h2; subst h1; exact hmem
  | electionTimeout k hk => exact key k _ rfl (fun _ _ hq => Event.noConfusion hq)
  | heartbeat k hk => exact key k _ rfl (fun _ _ hq => Event.noConfusion hq)
  | client k rid cmd hk => exact key k _ rfl (fun _ _ hq => Event.noConfusion hq)
  | crash k hk =>
      -- a crash writes no history, mints nothing and commits nothing
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro c k' e hm
        rw [crash_created] at hm; rw [crash_createTime, crash_clock]
        obtain ⟨t, h1, h2⟩ := h.createdTime c k' e hm
        exact ⟨t, h1, by omega⟩
      · intro L T c lg Q hm
        rw [crash_commits] at hm; rw [crash_commitTime, crash_clock]
        obtain ⟨t, h1, h2⟩ := h.commitsTime L T c lg Q hm
        exact ⟨t, h1, by omega⟩
      · intro c lg t hm
        rw [crash_commitTime] at hm; rw [crash_commits]
        exact h.commitTimeIsCommit c lg t hm
      · intro e t hm
        rw [crash_createTime] at hm; rw [crash_hist]
        exact h.createInvoke e t hm
      · intro c lg t hm k' e hk1 hk2 hget
        rw [crash_commitTime] at hm; rw [crash_createTime]
        exact h.commitCreate c lg t hm k' e hk1 hk2 hget
      · intro t i rid n r hm
        rw [crash_hist] at hm
        obtain ⟨c, lg, t', e, h1, h2, h3, h4, h5, h6, h7⟩ := h.respondCommitted t i rid n r hm
        exact ⟨c, lg, t', e, by rw [crash_commitTime]; exact h1, h2, h3, h4, h5, h6, h7⟩

theorem lInv_reachable {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) : LInv members w := by
  induction h with
  | init => exact lInv_init members
  | tail hr hs ih => exact lInv_step hnd hr ih hs


/-! ## Real time is respected -/

/--
**A request answered before another was submitted is ordered before it.**

Suppose the cluster answered `ridA` at index `nA` at time `tA`, and `ridB` was
submitted strictly later and eventually answered at index `nB`. Then
`nA < nB`.

The argument: if `nB ≤ nA`, then `ridB`'s entry was already committed at index
`nB` when `ridA` was answered — committed indices are downward closed and, by
`committed_unique`, an index determines its entry for ever. But nothing is
committed before it is minted, and nothing is minted before its client asked
for it, so `ridB` was submitted before `tA`, contradicting distinct request ids.
-/
theorem realtime {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w)
    (huniq : ∀ t₁ i₁ t₂ i₂ rid (cmd₁ cmd₂ : Command),
        HEvent.invoke t₁ i₁ rid cmd₁ ∈ w.hist →
        HEvent.invoke t₂ i₂ rid cmd₂ ∈ w.hist → t₁ = t₂)
    {tA iA ridA nA : Nat} {rA : Reply}
    {tB iB ridB : Nat} {cmdB : Command}
    {tB' iB' nB : Nat} {rB : Reply}
    (hA : HEvent.respond tA iA ridA nA rA ∈ w.hist)
    (hinvB : HEvent.invoke tB iB ridB cmdB ∈ w.hist)
    (hB : HEvent.respond tB' iB' ridB nB rB ∈ w.hist)
    (hlt : tA < tB) : nA < nB := by
  have linv := lInv_reachable hnd hrch
  obtain ⟨cA, lgA, tA', eA, hA1, hA2, hA3, hA4, hA5, hA6, _⟩ := linv.respondCommitted _ _ _ _ _ hA
  obtain ⟨cB, lgB, tB'', eB, hB1, hB2, hB3, hB4, hB5, hB6, _⟩ := linv.respondCommitted _ _ _ _ _ hB
  rcases Nat.lt_or_ge nA nB with hq | hq
  · exact hq
  · exfalso
    -- `nB` was already committed when `ridA` was answered
    obtain ⟨LA, TA, QA, hcmA⟩ := linv.commitTimeIsCommit _ _ _ hA1
    obtain ⟨LB, TB, QB, hcmB⟩ := linv.commitTimeIsCommit _ _ _ hB1
    obtain ⟨e₀, hg₀, hc₀⟩ := commit_covers hnd hrch hcmA hB3 (by omega)
    have hcB : Protocol.Committed w nB eB TB := ⟨LB, cB, lgB, QB, hcmB, hB4, hB5⟩
    have he : e₀ = eB := committed_unique hnd hrch hc₀ hcB
    subst he
    -- so it was minted, and therefore submitted, before `tA`
    obtain ⟨tc, hc1, hc2⟩ := linv.commitCreate _ _ _ hA1 nB e₀ hB3 (by omega) hg₀
    obtain ⟨i₀, hi₀⟩ := linv.createInvoke _ _ hc1
    rw [hB6] at hi₀
    have := huniq _ _ _ _ _ _ _ hi₀ hinvB
    omega

/-! ## The committed log, as a list -/

/-- The entries a log holds at indices `1 … n`. -/
def logEntries (lg : σ) (n : Nat) : List Entry :=
  (List.range n).filterMap (fun k => LogStore.get lg (k + 1))

theorem logEntries_cmds (lg : σ) (n : Nat) :
    (logEntries lg n).map Entry.cmd = cmdsUpTo lg n := by
  unfold logEntries cmdsUpTo
  rw [List.map_filterMap]

/-- With no holes below `n`, the list is exactly the log's first `n` entries. -/
theorem logEntries_full {lg : σ} : ∀ n : Nat,
    (∀ j, 1 ≤ j → j ≤ n → (LogStore.get lg j).isSome) →
    (logEntries lg n).length = n
      ∧ ∀ k, k < n → (logEntries lg n)[k]? = LogStore.get lg (k + 1) := by
  intro n
  induction n with
  | zero => intro _; exact ⟨rfl, fun k hk => absurd hk (by omega)⟩
  | succ n ih =>
      intro hs
      obtain ⟨hlen, hget⟩ := ih (fun j h1 h2 => hs j h1 (by omega))
      obtain ⟨e, he⟩ : ∃ e, LogStore.get lg (n + 1) = some e := by
        cases hq : LogStore.get lg (n + 1) with
        | none =>
            exfalso
            have := hs (n + 1) (by omega) (by omega)
            rw [hq] at this; exact Bool.noConfusion this
        | some e => exact ⟨e, rfl⟩
      have hsplit : logEntries lg (n + 1) = logEntries lg n ++ [e] := by
        unfold logEntries
        rw [List.range_succ, List.filterMap_append]
        simp [he]
      refine ⟨by rw [hsplit]; simp [hlen], ?_⟩
      intro k hk
      rw [hsplit]
      rcases Nat.lt_or_ge k n with hq | hq
      · rw [List.getElem?_append_left (by omega)]
        exact hget k hq
      · have hkn : k = n := by omega
        subst hkn
        rw [List.getElem?_append_right (by omega), hlen]
        simp [he]

theorem logEntries_take {lg : σ} {n m : Nat} (h : m ≤ n)
    (hs : ∀ j, 1 ≤ j → j ≤ m → (LogStore.get lg j).isSome) :
    (logEntries lg n).take m = logEntries lg m := by
  obtain ⟨tl, hsplit⟩ : ∃ tl, logEntries lg n = logEntries lg m ++ tl := by
    unfold logEntries
    rw [show n = m + (n - m) by omega, List.range_add, List.filterMap_append]
    exact ⟨_, rfl⟩
  rw [hsplit]
  exact List.take_left' (logEntries_full m hs).1


/-- The commit record reaching the highest index. -/
def maxCommit : List (Nat × σ × Nat) → Option (Nat × σ × Nat)
  | [] => none
  | r :: rs =>
      match maxCommit rs with
      | none => some r
      | some q => if q.1 < r.1 then some r else some q

theorem maxCommit_mem : ∀ (l : List (Nat × σ × Nat)) q, maxCommit l = some q → q ∈ l := by
  intro l
  induction l with
  | nil => intro q h; exact absurd h (by simp [maxCommit])
  | cons r rs ih =>
      intro q h
      rw [maxCommit] at h
      cases hq : maxCommit rs with
      | none => rw [hq] at h; simp only [Option.some.injEq] at h; exact h ▸ List.mem_cons_self
      | some p =>
          rw [hq] at h
          dsimp only at h
          split at h
          · simp only [Option.some.injEq] at h; exact h ▸ List.mem_cons_self
          · simp only [Option.some.injEq] at h
            exact List.mem_cons_of_mem _ (h ▸ ih p hq)

theorem maxCommit_ge : ∀ (l : List (Nat × σ × Nat)) r, r ∈ l →
    ∃ q, maxCommit l = some q ∧ r.1 ≤ q.1 := by
  intro l
  induction l with
  | nil => intro r h; exact absurd h (by simp)
  | cons a rs ih =>
      intro r hr
      rw [maxCommit]
      cases hq : maxCommit rs with
      | none =>
          rcases List.mem_cons.mp hr with h' | h'
          · exact ⟨a, rfl, by rw [h']; exact Nat.le_refl _⟩
          · obtain ⟨q, hq1, _⟩ := ih r h'
            rw [hq] at hq1; exact absurd hq1 (by simp)
      | some p =>
          dsimp only
          rcases List.mem_cons.mp hr with h' | h'
          · by_cases hlt : p.1 < a.1
            · rw [if_pos hlt]; exact ⟨a, rfl, by rw [h']; exact Nat.le_refl _⟩
            · rw [if_neg hlt]; exact ⟨p, rfl, by rw [h']; omega⟩
          · obtain ⟨q, hq1, hq2⟩ := ih r h'
            rw [hq] at hq1
            have hpq : p = q := Option.some.inj hq1
            subst hpq
            by_cases hlt : p.1 < a.1
            · rw [if_pos hlt]; exact ⟨a, rfl, by omega⟩
            · rw [if_neg hlt]; exact ⟨p, rfl, hq2⟩

/-! ## The theorem -/

/--
**Linearizability.**

There is one sequence of log entries `L` — the cluster's committed log — such
that:

1. **Every answer the cluster ever gave is the answer a single, sequential
   key/value store would have given.** The response to request `rid` at index
   `n` is what `Spec.applyCmd` returns for `L`'s `n`-th command, run on the
   state reached by executing the `n - 1` commands before it; and that `n`-th
   entry is the one `rid` submitted.

2. **That order never contradicts real time.** If the cluster answered one
   request strictly before another was submitted, the first request's position
   in `L` comes strictly before the second's.

3. **Every replica is somewhere along that same order.** Each node's key/value
   state is exactly the sequential specification run on a prefix of `L`.

The only assumption beyond reachability is that clients use distinct request
ids, which is what makes "the operation for `rid`" well defined.
-/
theorem linearizable {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) (hfresh : Protocol.FreshIds w) :
    ∃ L : List Entry,
      -- 1. every answer is the sequential specification's answer, at its place in `L`
      (∀ t rid n r, Protocol.Answered w t rid n r →
          ∃ e, L[n - 1]? = some e ∧ e.reqId = rid
            ∧ r = (Spec.applyCmd (Spec.run ((L.take (n - 1)).map Entry.cmd)) e.cmd).2)
      -- 2. `L` never contradicts real time
      ∧ (∀ tA ridA nA (rA : Reply) tB ridB tB' nB (rB : Reply),
          Protocol.Answered w tA ridA nA rA →
          Protocol.Submitted w tB ridB →
          Protocol.Answered w tB' ridB nB rB →
          tA < tB → nA < nB)
      -- 3. every replica has executed a prefix of `L`
      ∧ (∀ i, LawfulKVStore.toModel (w.nodes i).kv
            = Spec.run ((L.take (w.nodes i).lastApplied).map Entry.cmd)) := by
  have linv := lInv_reachable hnd hrch
  have huniq : ∀ t₁ i₁ t₂ i₂ rid (cmd₁ cmd₂ : Command),
      HEvent.invoke t₁ i₁ rid cmd₁ ∈ w.hist →
      HEvent.invoke t₂ i₂ rid cmd₂ ∈ w.hist → t₁ = t₂ := by
    intro t₁ i₁ t₂ i₂ rid cmd₁ cmd₂ h1 h2
    exact hfresh t₁ t₂ rid ⟨i₁, cmd₁, h1⟩ ⟨i₂, cmd₂, h2⟩
  have hrt : ∀ tA ridA nA (rA : Reply) tB ridB tB' nB (rB : Reply),
      Protocol.Answered w tA ridA nA rA →
      Protocol.Submitted w tB ridB →
      Protocol.Answered w tB' ridB nB rB →
      tA < tB → nA < nB := by
    rintro _ _ _ _ _ _ _ _ _ ⟨iA, hA⟩ ⟨iB, cmdB, hI⟩ ⟨iB', hB⟩ hlt
    exact realtime hnd hrch huniq hA hI hB hlt
  cases hmax : maxCommit w.commitTime with
  | none =>
      -- with nothing committed anywhere, nothing has been answered or applied
      have hnone : ∀ (c : Nat) (lg : σ) (t : Nat), (c, lg, t) ∉ w.commitTime := by
        intro c lg t hmem
        obtain ⟨q, hq1, _⟩ := maxCommit_ge w.commitTime (c, lg, t) hmem
        rw [hmax] at hq1
        simp at hq1
      have happ : ∀ i, (w.nodes i).lastApplied = 0 := by
        intro i
        rcases Nat.eq_zero_or_pos (w.nodes i).lastApplied with h0 | h0
        · exact h0
        · exfalso
          have hab := appliedBound_reachable hrch i
          have hb := (sInv_reachable hnd hrch).bound i
          obtain ⟨e, he⟩ : ∃ e, LogStore.get (w.full i) (w.nodes i).lastApplied = some e := by
            cases hq : LogStore.get (w.full i) (w.nodes i).lastApplied with
            | none =>
                exfalso
                have hli := full_lastIndex hrch i
                have := (LogStore.get_isSome_iff (w.full i)
                  (w.nodes i).lastApplied).mpr
                  ⟨by rw [full_firstIndex hrch i]; omega, by omega⟩
                rw [hq] at this; exact Bool.noConfusion this
            | some e => exact ⟨e, rfl⟩
          obtain ⟨T, hcom, _⟩ :=
            (sInv_reachable hnd hrch).cov i (w.nodes i).lastApplied e (by omega) he
          obtain ⟨L', c', lg', Q', hcm', _, _⟩ := hcom
          obtain ⟨t', ht', _⟩ := linv.commitsTime L' T c' lg' Q' hcm'
          exact hnone c' lg' t' ht'
      refine ⟨[], ?_, hrt, ?_⟩
      · rintro t rid n r ⟨i, hmem⟩
        exfalso
        obtain ⟨c, lg, t', e, h1, _⟩ := linv.respondCommitted _ _ _ _ _ hmem
        exact hnone c lg t' h1
      · intro i
        have := smRefines_reachable hnd hrch i
        unfold AppliedModel at this
        rw [this, happ i]
        rfl
  | some q =>
      obtain ⟨c, lg, tq⟩ := q
      obtain ⟨L₀, T₀, Q₀, hcm⟩ :=
        linv.commitTimeIsCommit c lg tq (maxCommit_mem _ _ hmax)
      have hcovE : ∀ j, 1 ≤ j → j ≤ c →
          ∃ e, LogStore.get lg j = some e ∧ Protocol.Committed w j e T₀ :=
        fun j h1 h2 => commit_covers hnd hrch hcm h1 h2
      have hcov : ∀ j, 1 ≤ j → j ≤ c → (LogStore.get lg j).isSome := by
        intro j h1 h2
        obtain ⟨e, he, _⟩ := hcovE j h1 h2
        rw [he]; rfl
      refine ⟨logEntries lg c, ?_, hrt, ?_⟩
      case refine_2 =>
        -- every replica has applied a prefix of the same order
        intro i
        have hab := appliedBound_reachable hrch i
        have hb := (sInv_reachable hnd hrch).bound i
        have hli := full_lastIndex hrch i
        have hnodeCov : ∀ k, 1 ≤ k → k ≤ (w.nodes i).lastApplied →
            ∃ e' T', LogStore.get (w.full i) k = some e' ∧ Protocol.Committed w k e' T' := by
          intro k hk1 hk2
          obtain ⟨e', he'⟩ : ∃ e', LogStore.get (w.full i) k = some e' := by
            cases hq : LogStore.get (w.full i) k with
            | none =>
                exfalso
                have := (LogStore.get_isSome_iff (w.full i) k).mpr
                  ⟨by rw [full_firstIndex hrch i]; omega, by omega⟩
                rw [hq] at this; exact Bool.noConfusion this
            | some e' => exact ⟨e', rfl⟩
          obtain ⟨T', hc', _⟩ := (sInv_reachable hnd hrch).cov i k e' (by omega) he'
          exact ⟨e', T', he', hc'⟩
        have hle : (w.nodes i).lastApplied ≤ c := by
          rcases Nat.eq_zero_or_pos (w.nodes i).lastApplied with h0 | h0
          · omega
          · obtain ⟨e', T', he', hc'⟩ := hnodeCov _ h0 (Nat.le_refl _)
            obtain ⟨L', c', lg', Q', hcm', hidx', _⟩ := hc'
            obtain ⟨t', ht', _⟩ := linv.commitsTime L' T' c' lg' Q' hcm'
            obtain ⟨q, hq1, hq2⟩ := maxCommit_ge w.commitTime (c', lg', t') ht'
            rw [hmax] at hq1
            have : (c, lg, tq) = q := Option.some.inj hq1
            rw [← this] at hq2
            omega
        have hagree : ∀ k, k ≤ (w.nodes i).lastApplied →
            LogStore.get lg k = LogStore.get (w.full i) k := by
          refine committed_prefix_agree hnd hrch ?_ ?_
          · intro k hk1 hk2
            obtain ⟨e', hg', hc'⟩ := hcovE k hk1 (by omega)
            exact ⟨e', T₀, hg', hc'⟩
          · exact hnodeCov
        have hmod := smRefines_reachable hnd hrch i
        unfold AppliedModel at hmod
        rw [hmod, logEntries_take hle (fun j h1 h2 => hcov j h1 (by omega)), logEntries_cmds,
          cmdsUpTo_congr (w.nodes i).lastApplied hagree]
      rintro t rid n r ⟨i, hmem⟩
      obtain ⟨cR, lgR, tR, e, h1, _, hn1, hnc, hgn, hrid, hspec⟩ :=
        linv.respondCommitted _ _ _ _ _ hmem
      obtain ⟨q', hq1, hq2⟩ := maxCommit_ge w.commitTime (cR, lgR, tR) h1
      rw [hmax] at hq1
      have hq' : (c, lg, tq) = q' := Option.some.inj hq1
      have hnc' : n ≤ c := by
        have hz : cR ≤ q'.1 := hq2
        rw [← hq'] at hz
        omega
      obtain ⟨L₁, T₁, Q₁, hcmR⟩ := linv.commitTimeIsCommit cR lgR tR h1
      have hagree : ∀ k, k ≤ n → LogStore.get lg k = LogStore.get lgR k := by
        refine committed_prefix_agree hnd hrch ?_ ?_
        · intro k hk1 hk2
          obtain ⟨e', hg', hc'⟩ := hcovE k hk1 (by omega)
          exact ⟨e', T₀, hg', hc'⟩
        · intro k hk1 hk2
          obtain ⟨e', hg', hc'⟩ := commit_covers hnd hrch hcmR hk1 (by omega)
          exact ⟨e', T₁, hg', hc'⟩
      refine ⟨e, ?_, hrid, ?_⟩
      · rw [(logEntries_full c hcov).2 (n - 1) (by omega),
          show n - 1 + 1 = n by omega, hagree n (Nat.le_refl _)]
        exact hgn
      · rw [hspec, logEntries_take (by omega) (fun j h1 h2 => hcov j h1 (by omega)),
          logEntries_cmds, cmdsUpTo_congr (n - 1) (fun k hk => hagree k (by omega))]

end Hist

end RaftKV.Proof
