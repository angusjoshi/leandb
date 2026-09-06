import RaftKV.Proof.SMS

/-!
# The applied prefix refines the sequential specification

`stateMachineSafety` says two replicas never apply *different entries* at one
index. This file turns that into the statement a client actually cares about:
what a replica answers is what the sequential key/value specification says,
run on the commands it has applied — so two replicas that have applied the same
number of entries answer every lookup identically.

The chain is
`KVStore.applyCmd` ⟶ `Spec.applyCmd` (`Storage/KV.lean`, once and for all)
⟶ `applyLoop` ⟶ `Spec.applyAll` (here) ⟶ the whole cluster (here).
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [LawfulLogStore σ] [KVStore κ]

/-- The commands a log holds at indices `1 … n`. -/
def cmdsUpTo (lg : σ) (n : Nat) : List Command :=
  (List.range n).filterMap (fun k => (LogStore.get lg (k + 1)).map Entry.cmd)

/-- Extending by one present entry appends its command. -/
theorem cmdsUpTo_succ {lg : σ} {n : Nat} {e : Entry} (h : LogStore.get lg (n + 1) = some e) :
    cmdsUpTo lg (n + 1) = cmdsUpTo lg n ++ [e.cmd] := by
  unfold cmdsUpTo
  rw [List.range_succ, List.filterMap_append]
  simp [h]

/-- Logs that agree up to `n` hold the same commands up to `n`. -/
theorem cmdsUpTo_congr {lg₁ lg₂ : σ} : ∀ (n : Nat),
    (∀ k, k ≤ n → LogStore.get lg₁ k = LogStore.get lg₂ k) →
    cmdsUpTo lg₁ n = cmdsUpTo lg₂ n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro h
      unfold cmdsUpTo at ih ⊢
      rw [List.range_succ, List.filterMap_append, List.filterMap_append,
        ih (fun k hk => h k (by omega))]
      simp only [List.filterMap_cons, List.filterMap_nil, h (n + 1) (Nat.le_refl _)]

section Lawful

variable [LawfulKVStore κ]

/-- The state machine's applied prefix. -/
def AppliedModel (s : NodeState σ κ) : Prop :=
  LawfulKVStore.toModel s.kv = Spec.run (cmdsUpTo s.log s.lastApplied)

/-- **`applyOne` keeps the state machine equal to the specification's run.** -/
theorem applyOne_refines (s : NodeState σ κ) (h : AppliedModel s) :
    AppliedModel (applyOne s).1 := by
  unfold AppliedModel at h ⊢
  rw [applyOne]
  cases hq : LogStore.get s.log (s.lastApplied + 1) with
  | none => exact h
  | some e =>
      dsimp only
      cases hkv : KVStore.applyCmd s.kv e.cmd with
      | mk kv' r =>
          dsimp only
          have hst : LawfulKVStore.toModel kv'
              = (Spec.applyCmd (LawfulKVStore.toModel s.kv) e.cmd).1 := by
            have := KVStore.applyCmd_state s.kv e.cmd
            rw [hkv] at this; exact this
          rw [hst, h, cmdsUpTo_succ hq]
          unfold Spec.run
          rw [Spec.applyAll_append]
          rfl

/-- **`applyLoop` keeps the state machine equal to the specification's run.** -/
theorem applyLoop_refines (f : Nat) (s : NodeState σ κ) (acc : List Action)
    (h : AppliedModel s) : AppliedModel (applyLoop f s acc).1 := by
  induction f generalizing s acc with
  | zero => rw [applyLoop]; exact h
  | succ n ih =>
      rw [applyLoop]
      split
      · exact ih _ _ (applyOne_refines s h)
      · exact h

theorem applyCommitted_refines (s : NodeState σ κ) (h : AppliedModel s) :
    AppliedModel (applyCommitted s).1 := applyLoop_refines _ s [] h

end Lawful


/-- How one step can move the state machine: not at all, or by draining the commit queue. -/
theorem step_kv_shape (s : NodeState σ κ) (ev : Event) :
    ((Protocol.step s ev).1.kv = s.kv ∧ (Protocol.step s ev).1.lastApplied = s.lastApplied)
      ∨ ∃ s' : NodeState σ κ, s'.kv = s.kv ∧ s'.lastApplied = s.lastApplied
          ∧ s'.log = (Protocol.step s ev).1.log
          ∧ (Protocol.step s ev).1.kv = (applyCommitted s').1.kv
          ∧ (Protocol.step s ev).1.lastApplied = (applyCommitted s').1.lastApplied := by
  cases ev with
  | recv src m =>
      cases m with
      | requestVote term c li lt =>
          left
          rw [Protocol.step, handleRequestVote]
          split
          · exact ⟨by simp, by simp⟩
          · dsimp only; split <;> exact ⟨by simp, by simp⟩
      | requestVoteResp term g =>
          left
          rw [Protocol.step, handleRequestVoteResp]
          split
          · exact ⟨by simp, by simp⟩
          · split
            · exact ⟨by simp, by simp⟩
            · dsimp only; split <;> (split <;> exact ⟨by simp, by simp⟩)
      | appendEntries term l pi pt es lc =>
          rw [Protocol.step, handleAppendEntries]
          split
          · exact Or.inl ⟨by simp, by simp⟩
          · dsimp only
            split
            · exact Or.inl ⟨by simp, by simp⟩
            · dsimp only
              exact Or.inr ⟨_, by simp, by simp, by simp, rfl, rfl⟩
      | appendEntriesResp term ok mi =>
          rw [Protocol.step, handleAppendEntriesResp]
          split
          · exact Or.inl ⟨by simp, by simp⟩
          · split
            · exact Or.inl ⟨by simp, by simp⟩
            · split
              · exact Or.inr ⟨_, by simp, by simp, by simp, rfl, rfl⟩
              · exact Or.inl ⟨by simp, by simp⟩
  | clientReq rid cmd =>
      rw [Protocol.step, handleClientReq]
      split
      · exact Or.inl ⟨by simp, by simp⟩
      · dsimp only
        exact Or.inr ⟨_, by simp, by simp, by simp, rfl, rfl⟩
  | electionTimeout =>
      left
      rw [Protocol.step]
      split
      · exact ⟨by simp, by simp⟩
      · rw [startElection]; dsimp only; split <;> exact ⟨by simp, by simp⟩
  | heartbeatTimeout =>
      left
      rw [Protocol.step]; split <;> exact ⟨by simp, by simp⟩

section Lawful

variable [LawfulKVStore κ]

/-- Every replica's state machine is the specification run on its applied prefix. -/
def SMRefines (w : World σ κ) : Prop := ∀ i, AppliedModel (w.nodes i)

/--
**The replicated state machine refines the sequential specification.**

In every reachable world, each replica's key/value state is exactly what the
sequential specification produces from the commands that replica has applied.
-/
theorem smRefines_reachable {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) : SMRefines w := by
  induction h with
  | init =>
      intro i
      unfold AppliedModel
      have h1 : (World.init (σ := σ) (κ := κ) members).nodes i
          = Protocol.initState { me := i, members := members } := rfl
      rw [h1]
      simp only [Protocol.initState]
      rw [LawfulKVStore.model_empty]
      rfl
  | @tail w0 w1 hr hs ih =>
      have hr1 : Reachable members w1 := Reachable.tail hr hs
      have hsi := sInv_reachable hnd hr
      have hab := appliedBound_reachable hr
      have key : ∀ (j : Nat) (ev : Event), w1 = w0.act j ev →
          (∀ src m', ev = Event.recv src m' → (src, j, m') ∈ w0.sent) → SMRefines w1 := by
        intro j ev hw hdel
        subst hw
        intro i
        by_cases hij : i = j
        · subst hij
          have hlog := step_log_below_applied hnd hr (j := i) (ev := ev) hdel
          have hpre : AppliedModel
              ({ (w0.nodes i) with log := (Protocol.step (w0.nodes i) ev).1.log }
                : NodeState σ κ) := by
            unfold AppliedModel
            dsimp only
            rw [cmdsUpTo_congr (lg₂ := (w0.nodes i).log) _ hlog]
            exact ih i
          rw [act_nodes_self]
          unfold AppliedModel
          rcases step_kv_shape (w0.nodes i) ev with ⟨hkv, hla⟩ | ⟨s', h1, h2, h3, h4, h5⟩
          · rw [hkv, hla, cmdsUpTo_congr _ hlog]
            exact ih i
          · have hs' : AppliedModel s' := by
              unfold AppliedModel
              rw [h1, h2, h3]
              exact hpre
            have := applyCommitted_refines s' hs'
            unfold AppliedModel at this
            rw [h4, h5, this]
            have hlogeq : (applyCommitted s').1.log = (Protocol.step (w0.nodes i) ev).1.log := by
              rw [← h3]; simp
            rw [hlogeq]
        · rw [act_nodes_ne _ _ _ hij]; exact ih i
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


/--
**The state machine still matches the run of the *new* log**, before the step's
own applications are taken into account. This is the hypothesis `step_reply`
needs: a step may splice the log, but never below what has already been applied.
-/
theorem step_appliedModel_pre {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) {j : Nat} {ev : Event}
    (hdel : ∀ src m', ev = Event.recv src m' → (src, j, m') ∈ w.sent) :
    AppliedModel ({ (w.nodes j) with
      log := (Protocol.step (w.nodes j) ev).1.log } : NodeState σ κ) := by
  unfold AppliedModel
  dsimp only
  rw [cmdsUpTo_congr (lg₂ := (w.nodes j).log) _ (step_log_below_applied hnd hrch hdel)]
  exact smRefines_reachable hnd hrch j

/--
**End to end: replicas that have applied the same number of entries answer
every lookup identically, and answer exactly what the sequential specification
says.**
-/
theorem replicas_agree {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) {i j : Nat}
    (heq : (w.nodes i).lastApplied = (w.nodes j).lastApplied) :
    LawfulKVStore.toModel (w.nodes i).kv = LawfulKVStore.toModel (w.nodes j).kv
      ∧ ∀ k, KVStore.find (w.nodes i).kv k = KVStore.find (w.nodes j).kv k := by
  have hsm := smRefines_reachable hnd hrch
  have hab := appliedBound_reachable hrch
  have hsi := sInv_reachable hnd hrch
  have hsms := stateMachineSafety hnd hrch
  -- the applied prefixes hold the same commands
  have hcmds : cmdsUpTo (w.nodes i).log (w.nodes i).lastApplied
      = cmdsUpTo (w.nodes j).log (w.nodes j).lastApplied := by
    rw [← heq]
    refine cmdsUpTo_congr _ ?_
    intro k hk
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; simp
    · obtain ⟨e₁, h1⟩ : ∃ e, LogStore.get (w.nodes i).log k = some e := by
        cases hq : LogStore.get (w.nodes i).log k with
        | none =>
            exfalso
            have := (LogStore.get_isSome_iff (w.nodes i).log k).mpr
              ⟨h0, by have := hab i; have := hsi.bound i; omega⟩
            rw [hq] at this; exact Bool.noConfusion this
        | some e => exact ⟨e, rfl⟩
      obtain ⟨e₂, h2⟩ : ∃ e, LogStore.get (w.nodes j).log k = some e := by
        cases hq : LogStore.get (w.nodes j).log k with
        | none =>
            exfalso
            have := (LogStore.get_isSome_iff (w.nodes j).log k).mpr
              ⟨h0, by have := hab j; have := hsi.bound j; omega⟩
            rw [hq] at this; exact Bool.noConfusion this
        | some e => exact ⟨e, rfl⟩
      rw [h1, h2, hsms i j k e₁ e₂ hk (by omega) h1 h2]
  have hmodel : LawfulKVStore.toModel (w.nodes i).kv = LawfulKVStore.toModel (w.nodes j).kv := by
    have h1 := hsm i
    have h2 := hsm j
    unfold AppliedModel at h1 h2
    rw [h1, h2, hcmds]
  exact ⟨hmodel, fun k => by rw [LawfulKVStore.model_find, LawfulKVStore.model_find, hmodel]⟩

end Lawful

end RaftKV.Proof
