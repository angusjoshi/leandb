import RaftKV.Proof.LeaderLog
import RaftKV.Proof.Commit

/-!
# Payloads are drawn from a recorded leader log

`step_appendEntries_payload` says a payload is a tail of the sender's log at the
instant of sending. `leaderLogOf` snapshots that very log at that very step.
Putting the two together turns "the sender's log at some past moment" — which
nothing can refer to later — into a concrete `leaderLogs` record.

This is what lets an acknowledgement mean *"my log agrees with that leader's, up
to here"*, which is the content the commit rule actually relies on.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [LawfulLogStore σ] [KVStore κ]

/-- Every replication payload is a tail of a recorded log of its sender. -/
def MsgFromLeaderLog (w : World σ κ) : Prop :=
  ∀ (src dst t l pi pt : Nat) (es : List Entry) (lc : Nat),
    (src, dst, Msg.appendEntries t l pi pt es lc) ∈ w.sent →
    ∃ lgL : σ, (src, t, lgL) ∈ w.leaderLogs
      ∧ (∀ (n : Nat) (e : Entry), es[n]? = some e →
          LogStore.get lgL (pi + 1 + n) = some e)
      ∧ (LogStore.termAt lgL pi).getD 0 = pt
      ∧ es.length = LogStore.lastIndex lgL - pi

theorem msgFromLeaderLog_init (members : List Nat) :
    MsgFromLeaderLog (σ := σ) (κ := κ) (World.init members) := by
  intro src dst t l pi pt es lc h; simp [World.init] at h

/-- **Preserved by every step.** -/
theorem msgFromLeaderLog_step {members : List Nat} {w w' : World σ κ}
    (hr : Reachable members w) (h : MsgFromLeaderLog w) (hs : Step members w w') :
    MsgFromLeaderLog w' := by
  have hr' : Reachable members w' := Reachable.tail hr hs
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev → MsgFromLeaderLog w' := by
    intro j ev hw
    subst hw
    intro src dst t l pi pt es lc hp
    rw [act_sent] at hp
    rcases List.mem_append.mp hp with hp' | hp'
    · obtain ⟨lgL, h1, h2, h3, h4⟩ := h src dst t l pi pt es lc hp'
      exact ⟨lgL, leaderLog_mono h1, h2, h3, h4⟩
    · rcases mem_sendsOf hp' with ⟨to, m, heq, hact⟩
      have hsj : src = j := congrArg (fun q => q.1) heq
      have hm : m = Msg.appendEntries t l pi pt es lc := by
        have := congrArg (fun q => q.2.2) heq; simpa using this.symm
      subst hm; subst hsj
      -- the sending step also snapshots the sender's log
      obtain ⟨hlead, hterm⟩ := step_appendEntries_leader hact
      obtain ⟨p0, hp0⟩ := step_appendEntries_payload hact
      simp only [appendEntriesTo] at hp0
      obtain ⟨htt, _, hpi, hpt, hes, _⟩ := Msg.appendEntries.inj hp0
      have hni : max (LogStore.sendFloor (Protocol.step (w.nodes src) ev).1.log)
          (PeerMap.get (Protocol.step (w.nodes src) ev).1.nextIndex p0
          (LogStore.lastIndex (Protocol.step (w.nodes src) ev).1.log + 1)) = pi + 1 := by
        rw [hpi]
        have := Nat.le_max_left (LogStore.sendFloor (Protocol.step (w.nodes src) ev).1.log)
          (PeerMap.get (Protocol.step (w.nodes src) ev).1.nextIndex p0
            (LogStore.lastIndex (Protocol.step (w.nodes src) ev).1.log + 1))
        have := LogStore.one_le_sendFloor (Protocol.step (w.nodes src) ev).1.log
        omega
      have hfloor : LogStore.sendFloor (Protocol.step (w.nodes src) ev).1.log ≤ pi + 1 := by
        rw [← hni]; exact Nat.le_max_left _ _
      have hfl : LogStore.firstIndex (Protocol.step (w.nodes src) ev).1.log ≤
          max (LogStore.sendFloor (Protocol.step (w.nodes src) ev).1.log)
            (PeerMap.get (Protocol.step (w.nodes src) ev).1.nextIndex p0
              (LogStore.lastIndex (Protocol.step (w.nodes src) ev).1.log + 1)) :=
        Nat.le_trans (LogStore.firstIndex_le_sendFloor _) (Nat.le_max_left _ _)
      refine ⟨fullStep w src ev, ?_, ?_, ?_, ?_⟩
      · rw [act_leaderLogs]
        refine List.mem_append_right _ ?_
        rw [← hterm]
        exact leaderLogOf_self hlead
      · intro n e hn
        rw [hes] at hn
        have h0 := appendEntriesTo_entries (s := (Protocol.step (w.nodes src) ev).1) (p := p0) hn
        rw [hni] at h0
        have := full_get_of hr' (i := src) (by rw [act_nodes_self]; exact h0)
        rwa [act_full_self] at this
      · -- `prevTerm` is read straight off the sender's own log
        have hb := full_termAt_getD hr' (i := src) (k := pi) ?_
        · rw [act_nodes_self, act_full_self] at hb
          rw [hb, hpt, ← hpi]
        · rw [act_nodes_self]
          rcases Nat.eq_zero_or_pos pi with hz | hz
          · exact Or.inl hz
          · exact Or.inr (Nat.le_of_lt_succ
              (LogStore.first_lt_of_sendFloor hfloor (by omega)))
      · -- the payload is the leader's entire tail
        have hlen := congrArg List.length
          (model_sliceFrom (Protocol.step (w.nodes src) ev).1.log _ hfl)
        simp only [List.length_map, List.length_drop] at hlen
        have hli := full_lastIndex hr' (i := src)
        rw [act_nodes_self, act_full_self] at hli
        rw [hes, hlen, hni, hli]
        simp [LogStore.lastIndex, model_size]
  cases hs with
  | deliver s d m hd hm => exact key d _ rfl
  | electionTimeout k hk => exact key k _ rfl
  | heartbeat k hk => exact key k _ rfl
  | client k rid cmd hk => exact key k _ rfl
  | crash k hk =>
      intro src dst t l pi pt es lc hp
      rw [crash_sent] at hp
      obtain ⟨lgL, h1, h2, h3, h4⟩ := h src dst t l pi pt es lc hp
      exact ⟨lgL, by rw [crash_leaderLogs]; exact h1, h2, h3, h4⟩
  | compact k hk =>
      intro src dst t l pi pt es lc hp
      rw [compactAt_sent] at hp
      obtain ⟨lgL, h1, h2, h3, h4⟩ := h src dst t l pi pt es lc hp
      exact ⟨lgL, by rw [compactAt_leaderLogs]; exact h1, h2, h3, h4⟩

theorem msgFromLeaderLog_reachable {members : List Nat} {w : World σ κ}
    (h : Reachable members w) : MsgFromLeaderLog w := by
  induction h with
  | init => exact msgFromLeaderLog_init members
  | tail hr hs ih => exact msgFromLeaderLog_step hr ih hs

/-! ## Acknowledgements mean agreement -/

/-- Every step that emits a positive acknowledgement is a `handleAppendEntries` success. -/
theorem step_ack_shape {s : NodeState σ κ} {ev : Event} {to t m : Nat}
    (h : Action.send to (Msg.appendEntriesResp t true m) ∈ (Protocol.step s ev).2) :
    ∃ (src l pi pt : Nat) (es : List Entry) (lc : Nat),
      ev = Event.recv src (Msg.appendEntries t l pi pt es lc)
      ∧ m = pi + es.length
      ∧ (Protocol.step s ev).1.log = appendFrom s.log (pi + 1) es
      ∧ pi ≤ LogStore.lastIndex s.log
      ∧ (pi ≠ 0 → LogStore.termAt s.log pi = some pt)
      ∧ LogStore.firstIndex s.log ≤ pi + 1
      ∧ Protocol.aeAccepts s t pi pt = true
      ∧ s.currentTerm ≤ t
      ∧ (Protocol.step s ev).1.role = Role.follower := by
  cases ev with
  | recv src msg =>
      cases msg with
      | requestVote a b c d =>
          rw [Protocol.step] at h
          rcases handleRequestVote_send_shape h with ⟨_, _, heq⟩
          exact absurd heq (by simp)
      | requestVoteResp a b => exact absurd h handleRequestVoteResp_no_aer
      | appendEntriesResp a b c => exact absurd h handleAppendEntriesResp_no_aer
      | installSnapshot a b c d e =>
          rw [Protocol.step] at h
          exact absurd h handleInstallSnapshot_no_send
      | appendEntries term l pi pt es lc =>
          rw [Protocol.step] at h ⊢
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := handleAppendEntries_ack h
          subst h1
          exact ⟨src, l, pi, pt, es, lc, rfl, h2, h3, h4, h5, h6, h7, h8, h9⟩
  | clientReq rid cmd =>
      rw [Protocol.step] at h
      exact absurd h handleClientReq_no_aer
  | electionTimeout =>
      rw [Protocol.step] at h
      split at h
      · simp at h
      · exact absurd h startElection_no_aer
  | heartbeatTimeout =>
      rw [Protocol.step] at h
      split at h
      · rcases broadcastAppend_shape h with ⟨_, _, _, _, _, _, heq⟩
        exact absurd heq (by simp)
      · simp at h

/--
**A positive acknowledgement means the follower's log agrees with the leader's
up to the acknowledged index.**

This is the content the commit rule relies on: a leader counting `matchIndex`
values is really counting replicas whose logs match its own.
-/
def AckAgrees (w : World σ κ) : Prop :=
  ∀ (v T m : Nat) (lgp : σ), (v, T, m, lgp) ∈ w.acks →
    m ≤ LogStore.lastIndex lgp
      ∧ ∃ (L : Nat) (lgL : σ), (L, T, lgL) ∈ w.leaderLogs
        ∧ m ≤ LogStore.lastIndex lgL
        ∧ ∀ k, k ≤ m → LogStore.get lgp k = LogStore.get lgL k

theorem ackAgrees_init (members : List Nat) :
    AckAgrees (σ := σ) (κ := κ) (World.init members) := by
  intro v T m lgp h; simp [World.init] at h

/--
**The core splice agreement.**

If a follower's log passes the consistency check against a leader's log, then
after splicing that leader's payload the two agree all the way to the end of
what was sent. Used both to prove `AckAgrees` and, separately, to attribute a
node's later contents.
-/
theorem splice_agrees {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) {lgv lgS : σ}
    (hwfV : WellFormedLog w lgv) (hwfS : WellFormedLog w lgS)
    {pi pt : Nat} {es : List Entry}
    (hbound : pi ≤ LogStore.lastIndex lgv)
    (hchk : pi ≠ 0 → LogStore.termAt lgv pi = some pt)
    (hSpt : (LogStore.termAt lgS pi).getD 0 = pt)
    (hS2 : ∀ (n : Nat) (e : Entry), es[n]? = some e → LogStore.get lgS (pi + 1 + n) = some e)
    (hwfNew : WellFormedLog w (appendFrom lgv (pi + 1) es)) :
    ∀ k, k ≤ pi + es.length →
      LogStore.get (appendFrom lgv (pi + 1) es) k = LogStore.get lgS k := by
  have hb : pi + 1 ≤ LogStore.lastIndex lgv + 1 := by omega
  have hfv := hwfV.nocompact
  have hfs := hwfS.nocompact
  have hbelow : ∀ k, k ≤ pi → LogStore.get lgv k = LogStore.get lgS k := by
    intro k hk
    rcases Nat.eq_zero_or_pos pi with h0 | h0
    · have : k = 0 := by omega
      subst this; simp
    · have hx := hchk (by omega)
      obtain ⟨x, hxg⟩ : ∃ x, LogStore.get lgv pi = some x := by
        unfold LogStore.termAt at hx
        cases hq : LogStore.get lgv pi with
        | none => rw [hq] at hx; simp at hx
        | some x => exact ⟨x, rfl⟩
      have hxt : x.term = pt := by
        unfold LogStore.termAt at hx; rw [hxg] at hx; simpa using hx
      have hptpos : 1 ≤ pt := by rw [← hxt]; exact wf_term_pos hrch hwfV hxg
      obtain ⟨y, hyg⟩ : ∃ y, LogStore.get lgS pi = some y := by
        cases hq : LogStore.get lgS pi with
        | none =>
            exfalso
            unfold LogStore.termAt at hSpt; rw [hq] at hSpt; simp at hSpt; omega
        | some y => exact ⟨y, rfl⟩
      have hyt : y.term = pt := by
        unfold LogStore.termAt at hSpt; rw [hyg] at hSpt; simpa using hSpt
      have hxy : x = y := wf_entry_unique hnd hrch hwfV hwfS hxg hyg (by rw [hxt, hyt])
      exact wf_matching hnd hrch hwfV hwfS hxg (hxy ▸ hyg) k hk
  intro k hk
  by_cases hlow : k ≤ pi
  · rw [appendFrom_get_of_lt es _ (pi + 1) k hb (by omega)]
    exact hbelow k hlow
  · have hn : k - (pi + 1) < es.length := by omega
    obtain ⟨en, hen⟩ : ∃ en, es[k - (pi + 1)]? = some en :=
      ⟨es[k - (pi + 1)], List.getElem?_eq_getElem hn⟩
    have hterm := appendFrom_termAt es lgv (pi + 1) (k - (pi + 1)) en hb (by omega) hen
    rw [show pi + 1 + (k - (pi + 1)) = k by omega] at hterm
    have hLk : LogStore.get lgS k = some en := by
      have := hS2 (k - (pi + 1)) en hen
      rwa [show pi + 1 + (k - (pi + 1)) = k by omega] at this
    obtain ⟨z, hzg⟩ : ∃ z, LogStore.get (appendFrom lgv (pi + 1) es) k = some z := by
      unfold LogStore.termAt at hterm
      cases hq : LogStore.get (appendFrom lgv (pi + 1) es) k with
      | none => rw [hq] at hterm; simp at hterm
      | some z => exact ⟨z, rfl⟩
    have hzt : z.term = en.term := by
      unfold LogStore.termAt at hterm; rw [hzg] at hterm; simpa using hterm
    have : z = en := wf_entry_unique hnd hrch hwfNew hwfS hzg hLk hzt
    rw [hzg, hLk, this]

/--
**The consistency check forces the sender's log to reach the splice point.**

A follower only accepts a payload whose `prevIdx` matches an entry it already
holds; entry terms are positive, so the sender's advertised term at `prevIdx`
cannot be the `0` that a missing entry would report.
-/
theorem prev_reach {members : List Nat} {w : World σ κ}
    (hr : Reachable members w) {lgv lgL : σ} (hwf : WellFormedLog w lgv)
    {pi pt : Nat}
    (hchk : pi ≠ 0 → LogStore.termAt lgv pi = some pt)
    (hL3 : (LogStore.termAt lgL pi).getD 0 = pt) :
    pi ≤ LogStore.lastIndex lgL := by
  rcases Nat.eq_zero_or_pos pi with h0 | h0
  · omega
  · have hx := hchk (by omega)
    obtain ⟨x, hxg⟩ : ∃ x, LogStore.get lgv pi = some x := by
      unfold LogStore.termAt at hx
      cases hq : LogStore.get lgv pi with
      | none => rw [hq] at hx; simp at hx
      | some x => exact ⟨x, rfl⟩
    have hxt : x.term = pt := by
      unfold LogStore.termAt at hx; rw [hxg] at hx; simpa using hx
    have hpos : 1 ≤ pt := by rw [← hxt]; exact wf_term_pos hr hwf hxg
    cases hq : LogStore.get lgL pi with
    | none =>
        exfalso
        unfold LogStore.termAt at hL3; rw [hq] at hL3; simp at hL3; omega
    | some y => exact ((LogStore.get_isSome_iff lgL pi).mp (by rw [hq]; rfl)).2

/-- **`AckAgrees` is preserved by every step.** -/
theorem ackAgrees_step {members : List Nat} {w w' : World σ κ}
    (hnd : members.Nodup) (hr : Reachable members w)
    (h : AckAgrees w) (hs : Step members w w') : AckAgrees w' := by
  have hr' : Reachable members w' := Reachable.tail hr hs
  have hmsg := msgFromLeaderLog_reachable hr
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev →
      (∀ src m', ev = Event.recv src m' → (src, j, m') ∈ w.sent) → AckAgrees w' := by
    intro j ev hw hdel
    subst hw
    intro v T m lgp hmem
    rcases List.mem_append.mp hmem with h' | h'
    · obtain ⟨hlen, L, lgL, h1, hlen2, h2⟩ := h v T m lgp h'
      exact ⟨hlen, L, lgL, leaderLog_mono h1, hlen2, h2⟩
    · rcases mem_ackOf_cases h' with ⟨to0, hact, hvj, hlg⟩ | ⟨hlead, hvj, hT, hm, hlg⟩
      case inr =>
        -- the leader's own standing acknowledgement of its whole log
        subst hvj; subst hT; subst hm; subst hlg
        refine ⟨Nat.le_refl _, v, _, ?_, Nat.le_refl _, fun k _ => rfl⟩
        rw [act_leaderLogs]
        exact List.mem_append_right _ (leaderLogOf_self hlead)
      subst hvj
      obtain ⟨src, l, pi, pt, es, lc, hev, hm, hlog, hpi0, hchk0, hfw, hacc, _, _⟩ :=
        step_ack_shape hact
      -- cross to the logical log, where the invariant lives
      have hfull : fullStep w v ev = appendFrom (w.full v) (pi + 1) es := by
        subst hev; rw [fullStep_node _ _ _ (by simp [Event.isSnapRecv]), nodeFullStep, if_pos hacc]
      have hpi : pi ≤ LogStore.lastIndex (w.full v) := by
        rw [full_lastIndex hr v]; exact hpi0
      have hchk : pi ≠ 0 → LogStore.termAt (w.full v) pi = some pt :=
        fun hz => full_termAt hr (hchk0 hz)
      have hf1 : LogStore.firstIndex (w.full v) = 1 := full_firstIndex hr v
      have hpkt := hdel src (Msg.appendEntries T l pi pt es lc) hev
      obtain ⟨lgL, hL1, hL2, hL3, hL4⟩ := hmsg src v T l pi pt es lc hpkt
      refine ⟨?_, src, lgL, leaderLog_mono hL1, ?_, ?_⟩
      · -- the splice reaches at least as far as was acknowledged
        have hlgp0 : lgp = appendFrom (w.full v) (pi + 1) es := by
          rw [hlg]; exact hfull
        rw [hlgp0]
        have := appendFrom_lastIndex_ge es (w.full v) (pi + 1) (by omega)
        omega
      · -- the payload is the sender's whole tail, so the ack reaches its end
        have hptpos : pi ≤ LogStore.lastIndex lgL := by
          rcases Nat.eq_zero_or_pos pi with h0 | h0
          · omega
          · have hx := hchk (by omega)
            obtain ⟨x, hxg⟩ : ∃ x, LogStore.get (w.full v) pi = some x := by
              unfold LogStore.termAt at hx
              cases hq : LogStore.get (w.full v) pi with
              | none => rw [hq] at hx; simp at hx
              | some x => exact ⟨x, rfl⟩
            have hxt : x.term = pt := by
              unfold LogStore.termAt at hx; rw [hxg] at hx; simpa using hx
            have hpos : 1 ≤ pt := by
              rw [← hxt]; exact wf_term_pos hr (wf_node hnd hr v) hxg
            cases hq : LogStore.get lgL pi with
            | none =>
                exfalso
                unfold LogStore.termAt at hL3; rw [hq] at hL3; simp at hL3; omega
            | some y =>
                exact ((LogStore.get_isSome_iff lgL pi).mp (by rw [hq]; rfl)).2
        omega
      -- well-formedness of the three logs involved
      have hwfPre : WellFormedLog w (w.full v) := wf_node hnd hr v
      have hwfL : WellFormedLog w lgL := leaderLogWF_reachable hnd hr src T lgL hL1
      have hbound : pi + 1 ≤ LogStore.lastIndex (w.full v) + 1 := by omega
      -- below the splice point the follower already agreed with the leader
      have hbelow : ∀ k, k ≤ pi → LogStore.get (w.full v) k = LogStore.get lgL k := by
        intro k hk
        rcases Nat.eq_zero_or_pos pi with h0 | h0
        · have : k = 0 := by omega
          subst this; simp
        · have hx := hchk (by omega)
          obtain ⟨x, hxg⟩ : ∃ x, LogStore.get (w.full v) pi = some x := by
            unfold LogStore.termAt at hx
            cases hq : LogStore.get (w.full v) pi with
            | none => rw [hq] at hx; simp at hx
            | some x => exact ⟨x, rfl⟩
          have hxt : x.term = pt := by
            unfold LogStore.termAt at hx; rw [hxg] at hx; simpa using hx
          have hptpos : 1 ≤ pt := by
            rw [← hxt]; exact wf_term_pos hr hwfPre hxg
          obtain ⟨y, hyg⟩ : ∃ y, LogStore.get lgL pi = some y := by
            cases hq : LogStore.get lgL pi with
            | none =>
                exfalso
                unfold LogStore.termAt at hL3; rw [hq] at hL3
                simp at hL3; omega
            | some y => exact ⟨y, rfl⟩
          have hyt : y.term = pt := by
            unfold LogStore.termAt at hL3; rw [hyg] at hL3; simpa using hL3
          have hxy : x = y := wf_entry_unique hnd hr hwfPre hwfL hxg hyg (by rw [hxt, hyt])
          exact wf_matching hnd hr hwfPre hwfL hxg (hxy ▸ hyg) k hk
      have hlgp : lgp = appendFrom (w.full v) (pi + 1) es := by rw [hlg]; exact hfull
      intro k hk
      rw [hlgp]
      by_cases hlow : k ≤ pi
      · rw [appendFrom_get_of_lt es _ (pi + 1) k hbound (by omega)]
        exact hbelow k hlow
      · -- inside the payload: the spliced entry is the leader's own
        have hn : k - (pi + 1) < es.length := by omega
        obtain ⟨en, hen⟩ : ∃ en, es[k - (pi + 1)]? = some en :=
          ⟨es[k - (pi + 1)], List.getElem?_eq_getElem hn⟩
        have hterm := appendFrom_termAt es (w.full v) (pi + 1) (k - (pi + 1)) en
          hbound (by omega) hen
        rw [show pi + 1 + (k - (pi + 1)) = k by omega] at hterm
        have hLk : LogStore.get lgL k = some en := by
          have := hL2 (k - (pi + 1)) en hen
          rwa [show pi + 1 + (k - (pi + 1)) = k by omega] at this
        obtain ⟨z, hzg⟩ : ∃ z, LogStore.get (appendFrom (w.full v) (pi + 1) es) k = some z := by
          unfold LogStore.termAt at hterm
          cases hq : LogStore.get (appendFrom (w.full v) (pi + 1) es) k with
          | none => rw [hq] at hterm; simp at hterm
          | some z => exact ⟨z, rfl⟩
        have hzt : z.term = en.term := by
          unfold LogStore.termAt at hterm; rw [hzg] at hterm; simpa using hterm
        have hwfNew : WellFormedLog (w.act v ev) (appendFrom (w.full v) (pi + 1) es) := by
          have h0 := wf_node hnd hr' v
          rw [act_full_self] at h0
          rwa [hfull] at h0
        have hwfL' : WellFormedLog (w.act v ev) lgL := hwfL.mono
        have : z = en := wf_entry_unique hnd hr' hwfNew hwfL' hzg hLk hzt
        rw [hzg, hLk, this]
  cases hs with
  | deliver s d m hd hmem =>
      refine key d _ rfl ?_
      intro src' m' heq
      have h1 : s = src' := (Event.recv.inj heq).1
      have h2 : m = m' := (Event.recv.inj heq).2
      subst h2; subst h1; exact hmem
  | electionTimeout k hk => exact key k _ rfl (fun _ _ hq => Event.noConfusion hq)
  | heartbeat k hk => exact key k _ rfl (fun _ _ hq => Event.noConfusion hq)
  | client k rid cmd hk => exact key k _ rfl (fun _ _ hq => Event.noConfusion hq)
  | crash k hk =>
      intro v T m lgp hm
      rw [crash_acks] at hm
      obtain ⟨hlen, L, lgL, h1, h2, h3⟩ := h v T m lgp hm
      exact ⟨hlen, L, lgL, by rw [crash_leaderLogs]; exact h1, h2, h3⟩
  | compact k hk =>
      intro v T m lgp hm
      rw [compactAt_acks] at hm
      obtain ⟨hlen, L, lgL, h1, h2, h3⟩ := h v T m lgp hm
      exact ⟨hlen, L, lgL, by rw [compactAt_leaderLogs]; exact h1, h2, h3⟩

/-- **Acknowledgements mean agreement, in every reachable world.** -/
theorem ackAgrees_reachable {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) : AckAgrees w := by
  induction h with
  | init => exact ackAgrees_init members
  | tail hr hs ih => exact ackAgrees_step hnd hr ih hs

/-! ## Commit records sit inside the leader's own log history -/

/-- A commit record's log is one of that leader's recorded logs. -/
def CommitIsLeaderLog (w : World σ κ) : Prop :=
  ∀ (L T c : Nat) (lg : σ) (Q : List Nat), (L, T, c, lg, Q) ∈ w.commits →
    (L, T, lg) ∈ w.leaderLogs ∧ LogStore.termAt lg c = some T

theorem commitIsLeaderLog_init (members : List Nat) :
    CommitIsLeaderLog (σ := σ) (κ := κ) (World.init members) := by
  intro L T c lg Q h; simp [World.init] at h

theorem commitIsLeaderLog_step {members : List Nat} {w w' : World σ κ}
    (hr : Reachable members w) (h : CommitIsLeaderLog w) (hs : Step members w w') :
    CommitIsLeaderLog w' := by
  have hr' : Reachable members w' := Reachable.tail hr hs
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev → CommitIsLeaderLog w' := by
    intro j ev hw
    subst hw
    intro L T c lg Q hmem
    rcases List.mem_append.mp hmem with h' | h'
    · obtain ⟨h1, h2⟩ := h L T c lg Q h'
      exact ⟨leaderLog_mono h1, h2⟩
    · obtain ⟨h1, h2, h3, h4, _, hlead, hadv⟩ := mem_commitOf h'
      subst h1
      refine ⟨?_, ?_⟩
      · rw [act_leaderLogs]
        refine List.mem_append_right _ ?_
        rw [h2, h4]
        exact leaderLogOf_self hlead
      · -- the committed index carries the leader's own term, by the commit rule
        rw [h3, h4, h2]
        have hb := commit_term_of_step (s := w.nodes L) (ev := ev) hlead hadv
        have hbb := full_termAt hr' (i := L) (k := (Protocol.step (w.nodes L) ev).1.commitIndex)
          (by rw [act_nodes_self]; exact hb)
        rwa [act_full_self] at hbb
  cases hs with
  | deliver s d m hd hm => exact key d _ rfl
  | electionTimeout k hk => exact key k _ rfl
  | heartbeat k hk => exact key k _ rfl
  | client k rid cmd hk => exact key k _ rfl
  | crash k hk =>
      intro L T c lg Q hm
      rw [crash_commits] at hm
      obtain ⟨h1, h2⟩ := h L T c lg Q hm
      exact ⟨by rw [crash_leaderLogs]; exact h1, h2⟩
  | compact k hk =>
      intro L T c lg Q hm
      rw [compactAt_commits] at hm
      obtain ⟨h1, h2⟩ := h L T c lg Q hm
      exact ⟨by rw [compactAt_leaderLogs]; exact h1, h2⟩

theorem commitIsLeaderLog_reachable {members : List Nat} {w : World σ κ}
    (h : Reachable members w) : CommitIsLeaderLog w := by
  induction h with
  | init => exact commitIsLeaderLog_init members
  | tail hr hs ih => exact commitIsLeaderLog_step hr ih hs

/--
**Durable commit evidence.**

For every commit record, a majority of nodes hold acknowledgement snapshots that
agree with the committing leader's log all the way up to the committed index —
and the committed entry there carries the leader's own term.
-/
theorem commit_ack_quorum {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w)
    {L T c : Nat} {lg : σ} {Q : List Nat} (hc : (L, T, c, lg, Q) ∈ w.commits) :
    LogStore.termAt lg c = some T
      ∧ (L, T, lg) ∈ w.leaderLogs := by
  exact ⟨(commitIsLeaderLog_reachable hrch L T c lg Q hc).2,
         (commitIsLeaderLog_reachable hrch L T c lg Q hc).1⟩

end RaftKV.Proof
