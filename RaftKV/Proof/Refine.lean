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

/--
The entries a log holds at indices `1 … n`.

Entries, not commands: duplicate suppression is keyed on the request id, so the
specification has to see it.
-/
def cmdsUpTo (lg : σ) (n : Nat) : List Entry :=
  (List.range n).filterMap (fun k => LogStore.get lg (k + 1))

/-- Extending by one present entry appends it. -/
theorem cmdsUpTo_succ {lg : σ} {n : Nat} {e : Entry} (h : LogStore.get lg (n + 1) = some e) :
    cmdsUpTo lg (n + 1) = cmdsUpTo lg n ++ [e] := by
  unfold cmdsUpTo
  rw [List.range_succ, List.filterMap_append]
  simp [h]

/-- Logs that agree up to `n` hold the same entries up to `n`. -/
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

/--
The state machine's applied prefix, measured against the **logical** log.

Compaction is why this is not measured against the node's own log: the entries
the snapshot covers are no longer there to run, but they did run.
-/
def AppliedModel (fl : σ) (s : NodeState σ κ) : Prop :=
  (⟨LawfulKVStore.toModel s.kv, fun q => s.sessions.contains q⟩ : Spec.KVModel)
    = Spec.runE (cmdsUpTo fl s.lastApplied)

/-- **`applyOne` keeps the state machine equal to the specification's run.** -/
theorem applyOne_refines (fl : σ) (s : NodeState σ κ)
    (hbr : ∀ k, LogStore.firstIndex s.log ≤ k → LogStore.get s.log k = LogStore.get fl k)
    (hfa : LogStore.firstIndex s.log ≤ s.lastApplied + 1)
    (h : AppliedModel fl s) : AppliedModel fl (applyOne s).1 := by
  unfold AppliedModel at h ⊢
  rw [applyOne]
  cases hq : LogStore.get s.log (s.lastApplied + 1) with
  | none => exact h
  | some e =>
      dsimp only
      rw [cmdsUpTo_succ (by rw [← hbr _ hfa]; exact hq)]
      unfold Spec.runE at h ⊢
      rw [Spec.applyAllE_append, ← h]
      show _ = (Spec.applyEntry
        ⟨LawfulKVStore.toModel s.kv, fun q => s.sessions.contains q⟩ e).1
      unfold Spec.applyEntry
      by_cases hdup : (Spec.isWrite e.cmd && s.sessions.contains e.reqId) = true
      · have hw : Spec.isWrite e.cmd = true := (Bool.and_eq_true .. |>.mp hdup).1
        have hc : s.sessions.contains e.reqId = true := (Bool.and_eq_true .. |>.mp hdup).2
        rw [if_pos hdup, if_pos hdup]
        have : (Spec.isWrite e.cmd && !s.sessions.contains e.reqId) = false := by
          rw [hc]; simp
        rw [this, if_neg (by simp)]
      · have hst : LawfulKVStore.toModel (KVStore.applyCmd s.kv e.cmd).1
            = (Spec.applyCmd (LawfulKVStore.toModel s.kv) e.cmd).1 :=
          KVStore.applyCmd_state s.kv e.cmd
        rw [if_neg hdup, if_neg hdup]
        refine congr (congrArg Spec.KVModel.mk hst) ?_
        funext q
        by_cases hw : Spec.isWrite e.cmd = true
        · have hc : s.sessions.contains e.reqId = false := by
            cases hcq : s.sessions.contains e.reqId with
            | false => rfl
            | true => exact absurd (by rw [hw, hcq]; rfl) hdup
          rw [if_pos (by rw [hw, hc]; rfl)]
          simp only [List.contains_cons, hw, Bool.true_and]
          exact Bool.or_comm _ _
        · have hw' : Spec.isWrite e.cmd = false := by simpa using hw
          rw [if_neg (by rw [hw']; simp)]
          simp [hw']

/-- **`applyLoop` keeps the state machine equal to the specification's run.** -/
theorem applyLoop_refines (fl : σ) (f : Nat) (s : NodeState σ κ) (acc : List Action)
    (hbr : ∀ k, LogStore.firstIndex s.log ≤ k → LogStore.get s.log k = LogStore.get fl k)
    (hfa : LogStore.firstIndex s.log ≤ s.lastApplied + 1)
    (h : AppliedModel fl s) : AppliedModel fl (applyLoop f s acc).1 := by
  induction f generalizing s acc with
  | zero => rw [applyLoop]; exact h
  | succ n ih =>
      rw [applyLoop]
      split
      · have hlog : (applyOne s).1.log = s.log := applyOne_log s
        have hla : s.lastApplied ≤ (applyOne s).1.lastApplied := applyOne_lastApplied_ge s
        exact ih (applyOne s).1 (acc ++ (applyOne s).2)
          (fun k hk => by rw [hlog] at hk ⊢; exact hbr k hk)
          (by rw [hlog]; omega)
          (applyOne_refines fl s hbr hfa h)
      · exact h

theorem applyCommitted_refines (fl : σ) (s : NodeState σ κ)
    (hbr : ∀ k, LogStore.firstIndex s.log ≤ k → LogStore.get s.log k = LogStore.get fl k)
    (hfa : LogStore.firstIndex s.log ≤ s.lastApplied + 1)
    (h : AppliedModel fl s) : AppliedModel fl (applyCommitted s).1 :=
  applyLoop_refines fl _ s [] hbr hfa h

end Lawful


/-- How one step can move the state machine: not at all, or by draining the commit queue. -/
theorem step_kv_shape (s : NodeState σ κ) (ev : Event) :
    ((Protocol.step s ev).1.kv = s.kv ∧ (Protocol.step s ev).1.lastApplied = s.lastApplied
        ∧ (Protocol.step s ev).1.sessions = s.sessions)
      ∨ (∃ s' : NodeState σ κ, s'.kv = s.kv ∧ s'.lastApplied = s.lastApplied
          ∧ s'.sessions = s.sessions
          ∧ s'.log = (Protocol.step s ev).1.log
          ∧ (Protocol.step s ev).1.kv = (applyCommitted s').1.kv
          ∧ (Protocol.step s ev).1.lastApplied = (applyCommitted s').1.lastApplied
          ∧ (Protocol.step s ev).1.sessions = (applyCommitted s').1.sessions
          ∧ ev.isSnapRecv = false)
      ∨ (∃ (src term lid lastIdx : Nat) (anchor : Entry) (pairs : List (String × String) × List Nat),
          ev = Event.recv src (Msg.installSnapshot term lid lastIdx anchor pairs)
          ∧ Protocol.snapInstalls s term lastIdx anchor = true
          ∧ (Protocol.step s ev).1.kv = KVStore.ofPairs pairs.1
          ∧ (Protocol.step s ev).1.lastApplied = lastIdx
          ∧ (Protocol.step s ev).1.sessions = pairs.2) := by
  cases ev with
  | recv src m =>
      cases m with
      | installSnapshot term lid lastIdx anchor pairs =>
          by_cases hi : Protocol.snapInstalls s term lastIdx anchor = true
          · refine Or.inr (Or.inr ⟨src, term, lid, lastIdx, anchor, pairs, rfl, hi,
              ?_, ?_, ?_⟩) <;>
              (have hlt : ¬ (term < s.currentTerm) := by
                 rw [Protocol.snapInstalls] at hi
                 simp only [Bool.and_eq_true, Bool.not_eq_true'] at hi
                 simpa using hi.1.1.1.1
               rw [Protocol.step, handleInstallSnapshot, if_neg hlt]
               dsimp only
               rw [if_pos hi])
          · left
            have hi' : Protocol.snapInstalls s term lastIdx anchor = false := by simpa using hi
            have hmsd : ∀ v, (maybeStepDown s term v).1.kv = s.kv
                ∧ (maybeStepDown s term v).1.lastApplied = s.lastApplied := by
              intro v; rw [maybeStepDown]; split <;> exact ⟨rfl, rfl⟩
            rw [Protocol.step, handleInstallSnapshot]
            by_cases hlt : term < s.currentTerm
            · rw [if_pos hlt]; exact ⟨rfl, rfl, rfl⟩
            · rw [if_neg hlt]
              dsimp only
              rw [if_neg (by simp [hi'])]
              refine ⟨(hmsd (some lid)).1, (hmsd (some lid)).2, ?_⟩
              show (maybeStepDown s term (some lid)).1.sessions = s.sessions
              rw [maybeStepDown]; split <;> rfl
      | requestVote term c li lt =>
          left
          rw [Protocol.step, handleRequestVote]
          split
          · exact ⟨by simp, by simp, by simp⟩
          · dsimp only; split <;> exact ⟨by simp, by simp, by simp⟩
      | requestVoteResp term g =>
          left
          rw [Protocol.step, handleRequestVoteResp]
          split
          · exact ⟨by simp, by simp, by simp⟩
          · split
            · exact ⟨by simp, by simp, by simp⟩
            · dsimp only; split <;> (split <;> exact ⟨by simp, by simp, by simp⟩)
      | appendEntries term l pi pt es lc =>
          rw [Protocol.step, handleAppendEntries]
          split
          · exact Or.inl ⟨by simp, by simp⟩
          · dsimp only
            split
            · exact Or.inl ⟨by simp, by simp⟩
            · dsimp only
              exact Or.inr (Or.inl ⟨_, by simp, by simp, by simp, by simp, rfl, rfl, rfl, rfl⟩)
      | appendEntriesResp term ok mi =>
          rw [Protocol.step, handleAppendEntriesResp]
          split
          · exact Or.inl ⟨by simp, by simp⟩
          · split
            · exact Or.inl ⟨by simp, by simp⟩
            · split
              · exact Or.inr (Or.inl ⟨_, by simp, by simp, by simp, by simp, rfl, rfl, rfl, rfl⟩)
              · exact Or.inl ⟨by simp, by simp⟩
  | clientReq rid cmd =>
      rw [Protocol.step, handleClientReq]
      split
      · exact Or.inl ⟨by simp, by simp⟩
      · dsimp only
        exact Or.inr (Or.inl ⟨_, by simp, by simp, by simp, by simp, rfl, rfl, rfl, rfl⟩)
  | electionTimeout =>
      left
      rw [Protocol.step]
      split
      · exact ⟨by simp, by simp, by simp⟩
      · rw [startElection]; dsimp only; split <;> exact ⟨by simp, by simp, by simp⟩
  | heartbeatTimeout =>
      left
      rw [Protocol.step]; split <;> exact ⟨by simp, by simp, by simp⟩

section Lawful

variable [LawfulKVStore κ]

/-- Every replica's state machine is the specification run on its applied prefix. -/
def SMRefines (w : World σ κ) : Prop := ∀ i, AppliedModel (w.full i) (w.nodes i)

/-- And its snapshot is the run of everything the snapshot covers. -/
def SnapRefines (w : World σ κ) : Prop :=
  ∀ i, (⟨LawfulKVStore.toModel (w.nodes i).snapKV,
        fun q => (w.nodes i).snapSessions.contains q⟩ : Spec.KVModel)
    = Spec.runE (cmdsUpTo (w.full i) (w.nodes i).snapIndex)

/--
The same for a recorded leader snapshot: the bindings it carries are the run of
the prefix it covers.

This is the state-machine half of snapshot transfer, and the reason a follower
that installs one ends up with the right state machine rather than merely a
plausible one. It is established when the record is written, from the recording
node's own `SnapRefines`, and needs `LawfulKVStore.model_pairs` — the one law
that says serialising and rebuilding a state machine is the identity on the
model.
-/
def SnapRecRefines (w : World σ κ) : Prop :=
  ∀ i T n ps (lg : σ), (i, T, n, ps, lg) ∈ w.snapLogs →
    (⟨LawfulKVStore.toModel (KVStore.ofPairs ps.1 : κ), fun q => ps.2.contains q⟩ : Spec.KVModel)
      = Spec.runE (cmdsUpTo lg n)

/--
**The replicated state machine refines the sequential specification.**

In every reachable world, each replica's key/value state is exactly what the
sequential specification produces from the commands that replica has applied.
-/
theorem smRefines_snap {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) :
    SMRefines w ∧ SnapRefines w ∧ SnapRecRefines w := by
  induction h with
  | init =>
      refine ⟨fun i => ?_, fun i => ?_, by intro i T n ps lg hm; simp [World.init] at hm⟩
      · unfold AppliedModel
        have h1 : (World.init (σ := σ) (κ := κ) members).nodes i
            = Protocol.initState { me := i, members := members } := rfl
        rw [h1]
        simp only [Protocol.initState]
        rw [LawfulKVStore.model_empty]
        rfl
      · have h1 : (World.init (σ := σ) (κ := κ) members).nodes i
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
          (∀ src m', ev = Event.recv src m' → (src, j, m') ∈ w0.sent) →
          SMRefines w1 ∧ SnapRefines w1 ∧ SnapRecRefines w1 := by
        intro j ev hw hdel
        subst hw
        have hlog : ∀ i, i = j → ∀ k, k ≤ (w0.nodes i).lastApplied →
            LogStore.get (fullStep w0 i ev) k
              = LogStore.get (w0.full i) k := by
          intro i hij; subst hij
          exact step_log_below_applied hnd hr (j := i) (ev := ev) hdel
        have hsm : SMRefines (w0.act j ev) := by
          intro i
          by_cases hij : i = j
          · subst hij
            rw [act_nodes_self, act_full_self]
            unfold AppliedModel
            have hlg := hlog i rfl
            rcases step_kv_shape (w0.nodes i) ev with ⟨hkv, hla, hse⟩ |
              ⟨s', h1, h2, hse0, h3, h4, h5, hse1, hsr0⟩ |
              ⟨src, term, lid, lastIdx, anchor, pairs, hev, hi, hkv, hla, hse⟩
            · rw [hkv, hla, hse, cmdsUpTo_congr _ hlg]
              exact ih.1 i
            · have hs' : AppliedModel (fullStep w0 i ev) s' := by
                unfold AppliedModel
                rw [h1, h2, hse0, cmdsUpTo_congr _ hlg]
                exact ih.1 i
              have hbr : ∀ k, LogStore.firstIndex s'.log ≤ k →
                  LogStore.get s'.log k
                    = LogStore.get (fullStep w0 i ev) k := by
                rw [h3]
                intro k hk
                have := full_get hr1 (i := i) (k := k) (by rw [act_nodes_self]; exact hk)
                rwa [act_nodes_self, act_full_self] at this
              have hfa : LogStore.firstIndex s'.log ≤ s'.lastApplied + 1 := by
                rw [h3, h2, step_firstIndex _ _ hsr0]
                exact full_applied hr i
              have hac := applyCommitted_refines _ s' hbr hfa hs'
              unfold AppliedModel at hac
              rw [h4, h5, hse1]
              exact hac
            · -- an installed snapshot: the record carries the right state machine
              subst hev
              obtain ⟨lg, hrec, hgetA, hlg1, hfl⟩ :=
                snapInstall_facts (fullBridge_reachable hr) (hdel src _ rfl) hi
              have hcu : cmdsUpTo (LogStore.truncFrom lg (lastIdx + 1)) lastIdx
                  = cmdsUpTo lg lastIdx :=
                cmdsUpTo_congr _ (fun k hk => by
                  rw [LogStore.get_truncFrom, if_pos (by omega)])
              rw [hkv, hla, hse, hfl, hcu]
              exact ih.2.2 _ _ _ _ _ hrec
          · rw [act_nodes_ne _ _ _ hij, act_full_ne _ _ _ hij]; exact ih.1 i
        have hsnapref : SnapRefines (w0.act j ev) := by
          intro i
          by_cases hij : i = j
          · subst hij
            rw [act_nodes_self, act_full_self]
            by_cases hsr : ev.isSnapRecv = false
            · rw [step_snapKV _ _ hsr, step_snapIndex _ _ hsr, step_snapSessions _ _ hsr]
              rw [cmdsUpTo_congr _ (fun k hk => hlog i rfl k
                (Nat.le_trans hk (full_snapIndex hr i)))]
              exact ih.2.1 i
            · -- a snapshot event: installed, or nothing about the snapshot moves
              have hsr' : ev.isSnapRecv = true := by simpa using hsr
              cases ev with
              | clientReq _ _ => exact absurd hsr' (by simp [Event.isSnapRecv])
              | electionTimeout => exact absurd hsr' (by simp [Event.isSnapRecv])
              | heartbeatTimeout => exact absurd hsr' (by simp [Event.isSnapRecv])
              | recv src m =>
                  cases m with
                  | requestVote _ _ _ _ => exact absurd hsr' (by simp [Event.isSnapRecv])
                  | requestVoteResp _ _ => exact absurd hsr' (by simp [Event.isSnapRecv])
                  | appendEntries _ _ _ _ _ _ =>
                      exact absurd hsr' (by simp [Event.isSnapRecv])
                  | appendEntriesResp _ _ _ =>
                      exact absurd hsr' (by simp [Event.isSnapRecv])
                  | installSnapshot term lid lastIdx anchor pairs =>
                      by_cases hi : Protocol.snapInstalls (w0.nodes i) term lastIdx anchor = true
                      · obtain ⟨lg, hrec, hgetA, hlg1, hfl⟩ :=
                          snapInstall_facts (fullBridge_reachable hr) (hdel src _ rfl) hi
                        obtain ⟨hlt2, _, _, _⟩ := snapInstalls_facts hi
                        have hkv : (Protocol.step (w0.nodes i)
                            (Event.recv src
                              (Msg.installSnapshot term lid lastIdx anchor pairs))).1.snapKV
                            = KVStore.ofPairs pairs.1 := by
                          rw [Protocol.step, handleInstallSnapshot, if_neg hlt2]
                          dsimp only
                          rw [if_pos hi]
                        have hsi : (Protocol.step (w0.nodes i)
                            (Event.recv src
                              (Msg.installSnapshot term lid lastIdx anchor pairs))).1.snapIndex
                            = lastIdx := by
                          rw [Protocol.step, handleInstallSnapshot, if_neg hlt2]
                          dsimp only
                          rw [if_pos hi]
                        have hss : (Protocol.step (w0.nodes i)
                            (Event.recv src
                              (Msg.installSnapshot term lid lastIdx anchor pairs))).1.snapSessions
                            = pairs.2 := by
                          rw [Protocol.step, handleInstallSnapshot, if_neg hlt2]
                          dsimp only
                          rw [if_pos hi]
                        have hcu : cmdsUpTo (LogStore.truncFrom lg (lastIdx + 1)) lastIdx
                            = cmdsUpTo lg lastIdx :=
                          cmdsUpTo_congr _ (fun k hk => by
                            rw [LogStore.get_truncFrom, if_pos (by omega)])
                        rw [hkv, hsi, hss, hfl, hcu]
                        exact ih.2.2 _ _ _ _ _ hrec
                      · have hi' : Protocol.snapInstalls (w0.nodes i) term lastIdx anchor
                            = false := by simpa using hi
                        obtain ⟨hlog', hsnapi, hla', hci'⟩ :=
                          handleInstallSnapshot_noop (w0.nodes i) term lid lastIdx anchor pairs hi'
                        have hkv : (Protocol.step (w0.nodes i)
                            (Event.recv src
                              (Msg.installSnapshot term lid lastIdx anchor pairs))).1.snapKV
                            = (w0.nodes i).snapKV := by
                          rw [Protocol.step, handleInstallSnapshot]
                          by_cases hlt : term < (w0.nodes i).currentTerm
                          · rw [if_pos hlt]
                          · rw [if_neg hlt]
                            dsimp only
                            rw [if_neg (by simp [hi'])]
                            rw [maybeStepDown]; split <;> rfl
                        have hfl : fullStep w0 i (Event.recv src
                            (Msg.installSnapshot term lid lastIdx anchor pairs)) = w0.full i := by
                          rw [Protocol.fullStep, if_neg hi]
                        have hsi2 : (Protocol.step (w0.nodes i)
                            (Event.recv src
                              (Msg.installSnapshot term lid lastIdx anchor pairs))).1.snapIndex
                            = (w0.nodes i).snapIndex := hsnapi
                        have hss2 : (Protocol.step (w0.nodes i)
                            (Event.recv src
                              (Msg.installSnapshot term lid lastIdx anchor
                                pairs))).1.snapSessions
                            = (w0.nodes i).snapSessions := by
                          rw [Protocol.step, handleInstallSnapshot]
                          by_cases hlt : term < (w0.nodes i).currentTerm
                          · rw [if_pos hlt]
                          · rw [if_neg hlt]
                            dsimp only
                            rw [if_neg (by simp [hi'])]
                            rw [maybeStepDown]; split <;> rfl
                        rw [hkv, hsi2, hss2, hfl]
                        exact ih.2.1 i
          · rw [act_nodes_ne _ _ _ hij, act_full_ne _ _ _ hij]; exact ih.2.1 i
        refine ⟨hsm, hsnapref, ?_⟩
        · -- the record written by this step is the node's own new snapshot
          intro i T n ps lg hm
          rw [act_snapLogs] at hm
          rcases List.mem_append.mp hm with hm' | hm'
          · exact ih.2.2 i T n ps lg hm'
          · rw [snapLogOf] at hm'
            split at hm'
            · rcases List.mem_singleton.mp hm' with hq
              have e1 := congrArg (fun r => r.1) hq
              have e3 := congrArg (fun r => r.2.2.1) hq
              have e4 := congrArg (fun r => r.2.2.2.1) hq
              have e5 := congrArg (fun r => r.2.2.2.2) hq
              simp only at e1 e3 e4 e5
              subst e1
              rw [e3, e4, e5, LawfulKVStore.model_pairs]
              have := hsnapref i
              rwa [act_nodes_self, act_full_self] at this
            · simp at hm'
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
          -- the state machine restarts from the snapshot, at the index it covers
          refine ⟨fun i => ?_, fun i => ?_, ?_⟩
          · unfold AppliedModel
            rw [crash_full]
            by_cases hik : i = k
            · subst hik
              rw [crash_nodes_self, restart_kv, restart_lastApplied,
                LawfulKVStore.model_pairs]
              exact ih.2.1 i
            · rw [crash_nodes_ne _ _ hik]; exact ih.1 i
          · rw [crash_full]
            by_cases hik : i = k
            · subst hik
              rw [crash_nodes_self, restart_snapKV, restart_snapIndex,
                LawfulKVStore.model_pairs]
              exact ih.2.1 i
            · rw [crash_nodes_ne _ _ hik]; exact ih.2.1 i
          · intro i T n ps lg hm; rw [crash_snapLogs] at hm; exact ih.2.2 i T n ps lg hm
      | compact k hk =>
          -- compaction leaves the state machine and the snapshot exactly where they were
          refine ⟨fun i => ?_, fun i => ?_, ?_⟩
          · unfold AppliedModel
            rw [compactAt_full]
            by_cases hik : i = k
            · subst hik
              rw [compactAt_nodes_self, compactTo_kv, compactTo_lastApplied,
                compactTo_sessions]
              exact ih.1 i
            · rw [compactAt_nodes_ne _ _ hik]; exact ih.1 i
          · rw [compactAt_full]
            by_cases hik : i = k
            · subst hik
              rw [compactAt_nodes_self]
              show (⟨LawfulKVStore.toModel (Protocol.compactTo (w0.nodes i)).snapKV,
                    fun q => (Protocol.compactTo (w0.nodes i)).snapSessions.contains q⟩
                  : Spec.KVModel)
                = Spec.runE (cmdsUpTo (w0.full i) (Protocol.compactTo (w0.nodes i)).snapIndex)
              rw [Protocol.compactTo]
              split
              · exact ih.1 i
              · exact ih.2.1 i
            · rw [compactAt_nodes_ne _ _ hik]; exact ih.2.1 i
          · intro i T n ps lg hm; rw [compactAt_snapLogs] at hm; exact ih.2.2 i T n ps lg hm

/--
**The replicated state machine refines the sequential specification.**

In every reachable world, each replica's key/value state is exactly what the
sequential specification produces from the commands that replica has applied.
-/
theorem smRefines_reachable {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) : SMRefines w :=
  (smRefines_snap hnd h).1

/--
**The state machine still matches the run of the *new* log**, before the step's
own applications are taken into account. This is the hypothesis `step_reply`
needs: a step may splice the log, but never below what has already been applied.
-/
theorem step_appliedModel_pre {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) {j : Nat} {ev : Event}
    (hdel : ∀ src m', ev = Event.recv src m' → (src, j, m') ∈ w.sent) :
    AppliedModel (fullStep w j ev) (w.nodes j) := by
  unfold AppliedModel
  rw [cmdsUpTo_congr (lg₂ := w.full j) _ (step_log_below_applied hnd hrch hdel)]
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
  have hcmds : cmdsUpTo (w.full i) (w.nodes i).lastApplied
      = cmdsUpTo (w.full j) (w.nodes j).lastApplied := by
    rw [← heq]
    refine cmdsUpTo_congr _ ?_
    intro k hk
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; simp
    · obtain ⟨e₁, h1⟩ : ∃ e, LogStore.get (w.full i) k = some e := by
        cases hq : LogStore.get (w.full i) k with
        | none =>
            exfalso
            have := (LogStore.get_isSome_iff (w.full i) k).mpr
              ⟨by rw [full_firstIndex hrch i]; omega,
                by have := hab i; have := hsi.bound i; omega⟩
            rw [hq] at this; exact Bool.noConfusion this
        | some e => exact ⟨e, rfl⟩
      obtain ⟨e₂, h2⟩ : ∃ e, LogStore.get (w.full j) k = some e := by
        cases hq : LogStore.get (w.full j) k with
        | none =>
            exfalso
            have := (LogStore.get_isSome_iff (w.full j) k).mpr
              ⟨by rw [full_firstIndex hrch j]; omega,
                by have := hab j; have := hsi.bound j; omega⟩
            rw [hq] at this; exact Bool.noConfusion this
        | some e => exact ⟨e, rfl⟩
      rw [h1, h2, hsms i j k e₁ e₂ hk (by omega) h1 h2]
  have hmodel : LawfulKVStore.toModel (w.nodes i).kv = LawfulKVStore.toModel (w.nodes j).kv := by
    have h1 := hsm i
    have h2 := hsm j
    unfold AppliedModel at h1 h2
    have h1' := congrArg Spec.KVModel.map h1
    have h2' := congrArg Spec.KVModel.map h2
    simp only at h1' h2'
    rw [h1', h2', hcmds]
  exact ⟨hmodel, fun k => by rw [LawfulKVStore.model_find, LawfulKVStore.model_find, hmodel]⟩

end Lawful

end RaftKV.Proof
