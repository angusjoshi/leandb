import RaftKV.Proof.Attribution

/-!
# Leader Completeness

The Figure-9 argument, by strong induction on the term.

An entry committed by the term-`T` leader sits in a majority of acknowledged
logs. Any later leader was elected by a majority, and the two majorities meet at
some node `v`. By `voteAttributed`, the log `v` held when it voted mirrors some
leader of a term in `[T, U)`; by the induction hypothesis that leader already
holds the committed prefix, so `v` did too. `vote_dominates` then carries the
prefix onto the new leader's log.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [LawfulLogStore σ] [KVStore κ]

/-- A quorum acknowledged index `c` in term `T`. -/
def AckQuorum (members : List Nat) (w : World σ κ) (T c : Nat) : Prop :=
  ∃ Q : List Nat, Q.Nodup ∧ (∀ p ∈ Q, p ∈ members)
    ∧ Q.length ≥ members.length / 2 + 1
    ∧ ∀ p ∈ Q, ∃ (m : Nat) (lgp : σ), (p, T, m, lgp) ∈ w.acks ∧ c ≤ m

/-- Two logs agree everywhere up to `c`. -/
def AgreeUpTo (lg₁ lg₂ : σ) (c : Nat) : Prop :=
  ∀ k, k ≤ c → LogStore.get lg₁ k = LogStore.get lg₂ k

/-- Every acknowledged log for a term agrees with the leader's up to what it acknowledged. -/
theorem ack_agrees_leader {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w)
    {L T c : Nat} {lgL : σ} (hL : (L, T, lgL) ∈ w.leaderLogs)
    (hcT : LogStore.termAt lgL c = some T)
    {p m : Nat} {lgp : σ} (hp : (p, T, m, lgp) ∈ w.acks) (hcm : c ≤ m) :
    AgreeUpTo lgp lgL c := by
  obtain ⟨hlen, L', lgL', h1, _, h2⟩ := ackAgrees_reachable hnd hrch p T m lgp hp
  have hLL := llInv_reachable hnd hrch
  have hL1 : (L, T) ∈ w.led := hLL.led L T lgL hL
  have hL2' : (L', T) ∈ w.led := hLL.led L' T lgL' h1
  have hLeq : L' = L := led_unique hnd hrch hL2' hL1
  obtain ⟨ec, hec⟩ : ∃ ec, LogStore.get lgL c = some ec := by
    unfold LogStore.termAt at hcT
    cases hq : LogStore.get lgL c with
    | none => rw [hq] at hcT; simp at hcT
    | some ec => exact ⟨ec, rfl⟩
  -- the acknowledged log itself reaches `c`
  obtain ⟨ep, hep⟩ : ∃ ep, LogStore.get lgp c = some ep := by
    cases hq : LogStore.get lgp c with
    | none =>
        exfalso
        rcases Nat.eq_zero_or_pos c with h0 | h0
        · rw [h0] at hec; simp at hec
        · have := (LogStore.get_isSome_iff lgp c).mpr ⟨by omega, by omega⟩
          rw [hq] at this; exact Bool.noConfusion this
    | some ep => exact ⟨ep, rfl⟩
  have hepL : LogStore.get lgL' c = some ep := by rw [← h2 c hcm]; exact hep
  -- combine the two snapshots of the same leader and term
  subst hLeq
  obtain ⟨lgM, hM, hM1, hM2⟩ :=
    leaderLog_both hnd hrch h1 hL (k₁ := c) (k₂ := c) hepL hec
  have hepc : ep = ec := by rw [hM1] at hM2; exact Option.some.inj hM2
  subst hepc
  have hwfp : WellFormedLog w lgp := (snapWF_reachable hnd hrch).2.1 p T m lgp hp
  have hwfL' : WellFormedLog w lgL' := leaderLogWF_reachable hnd hrch _ T lgL' h1
  have hwfL : WellFormedLog w lgL := leaderLogWF_reachable hnd hrch _ T lgL hL
  have hagree : ∀ k, k ≤ c → LogStore.get lgL' k = LogStore.get lgL k :=
    wf_matching hnd hrch hwfL' hwfL hepL hec
  intro k hk
  rw [h2 k (by omega), hagree k hk]

/-- The up-to-dateness relation the `upToDate` check computes. -/
def AsUpToDate (lg₁ lg₂ : σ) : Prop :=
  LogStore.lastTerm lg₁ > LogStore.lastTerm lg₂
    ∨ (LogStore.lastTerm lg₁ = LogStore.lastTerm lg₂
        ∧ LogStore.lastIndex lg₁ ≥ LogStore.lastIndex lg₂)

/-- Any entry of a well-formed log sits in a recorded log of its own term's leader. -/
theorem entry_in_leaderLog {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) {lg : σ}
    (hwf : WellFormedLog w lg) {k : Nat} {e : Entry} (hg : LogStore.get lg k = some e) :
    ∃ (Y : Nat) (lgY : σ), (Y, e.term, lgY) ∈ w.leaderLogs ∧ LogStore.get lgY k = some e := by
  obtain ⟨c, hc⟩ := hwf.created k e hg
  obtain ⟨lgY, h1, h2⟩ := (llInv_reachable hnd hrch).created c k e hc
  exact ⟨c, lgY, h1, h2⟩

/-- Log entries of the last index realise the last term. -/
theorem lastEntry {lg : σ} (h : 1 ≤ LogStore.lastIndex lg) :
    ∃ x : Entry, LogStore.get lg (LogStore.lastIndex lg) = some x
      ∧ x.term = LogStore.lastTerm lg := by
  cases hq : LogStore.get lg (LogStore.lastIndex lg) with
  | none =>
      exfalso
      have := (LogStore.get_isSome_iff lg (LogStore.lastIndex lg)).mpr ⟨by omega, Nat.le_refl _⟩
      rw [hq] at this; exact Bool.noConfusion this
  | some x =>
      exact ⟨x, rfl, by unfold LogStore.lastTerm LogStore.termAt; rw [hq]; rfl⟩

/--
**Domination carries a committed prefix.**

If `lgv` already agrees with the leader's log up to a committed index `c`, and
`lgd` is at least as up to date as `lgv`, then `lgd` agrees up to `c` too.

This is the Figure-9 two-case argument. When `lgd`'s last term is strictly
greater, its last entry belongs to a later leader which already holds the
committed prefix. When the last terms are equal, both logs end inside the same
term's block, so the longer one contains the shorter.
-/
theorem dominate_carries {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w)
    {lgv lgd lgL : σ} {c T : Nat}
    (hwfv : WellFormedLog w lgv) (hwfd : WellFormedLog w lgd) (hwfL : WellFormedLog w lgL)
    (hcT : LogStore.termAt lgL c = some T)
    (hv : AgreeUpTo lgv lgL c)
    (hdom : AsUpToDate lgd lgv) {N : Nat} (hN : LogStore.lastTerm lgd ≤ N)
    (hlater : ∀ (Y tY : Nat) (lgY : σ), (Y, tY, lgY) ∈ w.leaderLogs → T < tY → tY ≤ N →
        AgreeUpTo lgY lgL c) :
    AgreeUpTo lgd lgL c := by
  obtain ⟨ec, hec⟩ : ∃ ec, LogStore.get lgL c = some ec := by
    unfold LogStore.termAt at hcT
    cases hq : LogStore.get lgL c with
    | none => rw [hq] at hcT; simp at hcT
    | some ec => exact ⟨ec, rfl⟩
  have hect : ec.term = T := by
    unfold LogStore.termAt at hcT; rw [hec] at hcT; simpa using hcT
  have hvc : LogStore.get lgv c = some ec := by rw [hv c (Nat.le_refl _)]; exact hec
  have hc1 : 1 ≤ c := ((LogStore.get_isSome_iff lgv c).mp (by rw [hvc]; rfl)).1
  have hvlen : c ≤ LogStore.lastIndex lgv :=
    ((LogStore.get_isSome_iff lgv c).mp (by rw [hvc]; rfl)).2
  have hvterm : T ≤ LogStore.lastTerm lgv := by
    rw [← hect]; exact wf_le_lastTerm hnd hrch hwfv hvc
  have hdlen1 : 1 ≤ LogStore.lastIndex lgd := by
    rcases hdom with hgt | ⟨_, hge⟩
    · rcases Nat.eq_zero_or_pos (LogStore.lastIndex lgd) with h0 | h0
      · exfalso
        have : LogStore.lastTerm lgd = 0 := by
          unfold LogStore.lastTerm LogStore.termAt; rw [h0]; simp
        omega
      · exact h0
    · omega
  obtain ⟨xd, hxd, hxdt⟩ := lastEntry (σ := σ) (lg := lgd) hdlen1
  rcases Nat.lt_or_ge T xd.term with hlt | hle
  · -- a strictly later term: its own leader already holds the prefix
    obtain ⟨Y, lgY, hY1, hY3⟩ := entry_in_leaderLog hnd hrch hwfd hxd
    have hYagree : AgreeUpTo lgY lgL c := hlater Y xd.term lgY hY1 hlt (by omega)
    have hwfY : WellFormedLog w lgY := leaderLogWF_reachable hnd hrch _ _ lgY hY1
    have hmatch := wf_matching hnd hrch hwfd hwfY hxd hY3
    have hYc : LogStore.get lgY c = some ec := by rw [hYagree c (Nat.le_refl _)]; exact hec
    have hdc : c ≤ LogStore.lastIndex lgd := by
      rcases Nat.lt_or_ge (LogStore.lastIndex lgd) c with h1 | h2
      · exfalso
        have hYx : LogStore.get lgY (LogStore.lastIndex lgd) = some xd := by
          rw [← hmatch (LogStore.lastIndex lgd) (Nat.le_refl _)]; exact hxd
        have := wf_sorted hnd hrch hwfY hYx hYc (by omega)
        omega
      · exact h2
    intro k hk
    rw [hmatch k (by omega), hYagree k hk]
  · -- the same term: both logs end inside that leader's own block
    have hxdT : xd.term = T := by
      rcases hdom with hgt | ⟨heqt, _⟩ <;> omega
    -- combine the two term-`T` snapshots holding `xd` and `ec`
    obtain ⟨Y, lgY, hY1, hY3⟩ := entry_in_leaderLog hnd hrch hwfd hxd
    obtain ⟨Z, lgZ, hZ1, hZ3⟩ := entry_in_leaderLog hnd hrch hwfv hvc
    have hYT : (Y, T) ∈ w.led := by
      have := (llInv_reachable hnd hrch).led Y xd.term lgY hY1
      rwa [hxdT] at this
    have hZT : (Z, T) ∈ w.led := by
      have := (llInv_reachable hnd hrch).led Z ec.term lgZ hZ1
      rwa [hect] at this
    have hYZ : Y = Z := led_unique hnd hrch hYT hZT
    subst hYZ
    have hY1' : (Y, T, lgY) ∈ w.leaderLogs := by rw [← hxdT]; exact hY1
    have hZ1' : (Y, T, lgZ) ∈ w.leaderLogs := by rw [← hect]; exact hZ1
    obtain ⟨lgM, hM, hM1, hM2⟩ := leaderLog_both hnd hrch hY1' hZ1' hY3 hZ3
    have hwfM : WellFormedLog w lgM := leaderLogWF_reachable hnd hrch _ _ lgM hM
    have hdM := wf_matching hnd hrch hwfd hwfM hxd hM1
    have hML := wf_matching hnd hrch hwfM hwfL hM2 hec
    have hdc : c ≤ LogStore.lastIndex lgd := by
      rcases hdom with hgt | ⟨_, hge⟩
      · omega
      · omega
    intro k hk
    rw [hdM k (by omega), hML k hk]

/-! ## Durable election evidence -/

/-- Every grant on the wire has a vote-log snapshot behind it. -/
def GrantHasVoteLog (w : World σ κ) : Prop :=
  ∀ (v c t : Nat), (v, c, Msg.requestVoteResp t true) ∈ w.sent →
    ∃ lgv : σ, (v, t, lgv) ∈ w.voteLogs

theorem grantHasVoteLog_init (members : List Nat) :
    GrantHasVoteLog (σ := σ) (κ := κ) (World.init members) := by
  intro v c t h; simp [World.init] at h

theorem grantHasVoteLog_step {members : List Nat} {w w' : World σ κ}
    (h : GrantHasVoteLog w) (hs : Step members w w') : GrantHasVoteLog w' := by
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev → GrantHasVoteLog w' := by
    intro j ev hw
    subst hw
    intro v c t hp
    rw [act_sent] at hp
    rw [act_voteLogs]
    rcases List.mem_append.mp hp with hp' | hp'
    · obtain ⟨lgv, hlgv⟩ := h v c t hp'
      exact ⟨lgv, List.mem_append_left _ hlgv⟩
    · rcases mem_sendsOf hp' with ⟨to, m, heq, hact⟩
      have hvj : v = j := congrArg (fun q => q.1) heq
      have hm : m = Msg.requestVoteResp t true := by
        have := congrArg (fun q => q.2.2) heq; simpa using this.symm
      subst hm; subst hvj
      refine ⟨(Protocol.step (w.nodes v) ev).1.log, List.mem_append_right _ ?_⟩
      unfold voteLogOf
      exact List.mem_filterMap.mpr
        ⟨Action.send to (Msg.requestVoteResp t true), hact, rfl⟩
  cases hs with
  | deliver s d m hd hm => exact key d _ rfl
  | electionTimeout k hk => exact key k _ rfl
  | heartbeat k hk => exact key k _ rfl
  | client k rid cmd hk => exact key k _ rfl

theorem grantHasVoteLog_reachable {members : List Nat} {w : World σ κ}
    (h : Reachable members w) : GrantHasVoteLog w := by
  induction h with
  | init => exact grantHasVoteLog_init members
  | tail _ hs ih => exact grantHasVoteLog_step ih hs

/-- Every election record carries the quorum of grants that produced it. -/
def ElectedQuorum (members : List Nat) (w : World σ κ) : Prop :=
  ∀ X U (lgel : σ), (X, U, lgel) ∈ w.elected →
    ∃ V : List Nat, V.Nodup ∧ (∀ v ∈ V, v ∈ members)
      ∧ V.length ≥ members.length / 2 + 1
      ∧ ∀ v ∈ V, v = X ∨ (v, X, Msg.requestVoteResp U true) ∈ w.sent

theorem electedQuorum_init (members : List Nat) :
    ElectedQuorum (σ := σ) (κ := κ) members (World.init members) := by
  intro X U lgel h; simp [World.init] at h

theorem electedQuorum_step {members : List Nat} {w w' : World σ κ}
    (hnd : members.Nodup) (hr : Reachable members w)
    (h : ElectedQuorum members w) (hs : Step members w w') : ElectedQuorum members w' := by
  have hr' : Reachable members w' := Reachable.tail hr hs
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev → ElectedQuorum members w' := by
    intro j ev hw
    subst hw
    intro X U lgel hmem
    rcases List.mem_append.mp hmem with h' | h'
    · obtain ⟨V, h1, h2, h3, h4⟩ := h X U lgel h'
      exact ⟨V, h1, h2, h3, fun v hv => (h4 v hv).imp id witness_mono⟩
    · obtain ⟨he1, he2, _, he4, _⟩ := mem_electedOf h'
      subst he1
      have ha := allInv_reachable hr'
      have hlead : ((w.act X ev).nodes X).role = Role.leader := by
        rw [act_nodes_self]; exact he4
      obtain ⟨_, hnd', hsub, hwit⟩ :=
        ha.leader.votes X (by rw [hlead]; exact fun hq => Role.noConfusion hq)
      refine ⟨((w.act X ev).nodes X).votesGranted, hnd', hsub,
        ha.leader.quorum X hlead, ?_⟩
      intro v hv
      have := hwit v hv
      rw [act_nodes_self] at this
      rw [he2]
      exact this
  cases hs with
  | deliver s d m hd hm => exact key d _ rfl
  | electionTimeout k hk => exact key k _ rfl
  | heartbeat k hk => exact key k _ rfl
  | client k rid cmd hk => exact key k _ rfl

theorem electedQuorum_reachable {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) : ElectedQuorum members w := by
  induction h with
  | init => exact electedQuorum_init members
  | tail hr hs ih => exact electedQuorum_step hnd hr ih hs

/-! ## Vote-log well-formedness -/

theorem mem_voteLogOf {i v t : Nat} {lg : σ} {s : NodeState σ κ} {acts : List Action}
    (h : (v, t, lg) ∈ voteLogOf i s acts) : v = i ∧ lg = s.log := by
  unfold voteLogOf at h
  rcases List.mem_filterMap.mp h with ⟨a, _, heq⟩
  cases a with
  | reply _ _ _ => simp at heq
  | notLeader _ _ => simp at heq
  | send to msg =>
      cases msg with
      | requestVote a b c d => simp at heq
      | appendEntries a b c d e f => simp at heq
      | appendEntriesResp a b c => simp at heq
      | requestVoteResp t2 g =>
          cases g with
          | false => simp at heq
          | true =>
              simp only [Option.some.injEq, Prod.mk.injEq] at heq
              exact ⟨heq.1.symm, heq.2.2.symm⟩

/-- Every vote-time snapshot is a well-formed log. -/
def VoteLogWF (w : World σ κ) : Prop :=
  ∀ v t (lg : σ), (v, t, lg) ∈ w.voteLogs → WellFormedLog w lg

theorem voteLogWF_init (members : List Nat) :
    VoteLogWF (σ := σ) (κ := κ) (World.init members) := by
  intro v t lg h; simp [World.init] at h

theorem voteLogWF_step {members : List Nat} {w w' : World σ κ}
    (hnd : members.Nodup) (hr : Reachable members w)
    (h : VoteLogWF w) (hs : Step members w w') : VoteLogWF w' := by
  have hr' : Reachable members w' := Reachable.tail hr hs
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev → VoteLogWF w' := by
    intro j ev hw
    subst hw
    intro v t lg hmem
    rw [act_voteLogs] at hmem
    rcases List.mem_append.mp hmem with h' | h'
    · exact (h v t lg h').mono
    · obtain ⟨_, h2⟩ := mem_voteLogOf h'
      have hq : ((w.act j ev).nodes j).log = lg := by rw [act_nodes_self]; exact h2.symm
      rw [← hq]; exact wf_node hnd hr' j
  cases hs with
  | deliver s d m hd hm => exact key d _ rfl
  | electionTimeout k hk => exact key k _ rfl
  | heartbeat k hk => exact key k _ rfl
  | client k rid cmd hk => exact key k _ rfl

theorem voteLogWF_reachable {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) : VoteLogWF w := by
  induction h with
  | init => exact voteLogWF_init members
  | tail hr hs ih => exact voteLogWF_step hnd hr ih hs

/-! ## Election records are leader-log snapshots -/

/-- The log a node was elected with is one of its recorded leader logs. -/
def ElectedIsLeaderLog (w : World σ κ) : Prop :=
  ∀ X U (lg : σ), (X, U, lg) ∈ w.elected → (X, U, lg) ∈ w.leaderLogs

theorem electedIsLeaderLog_init (members : List Nat) :
    ElectedIsLeaderLog (σ := σ) (κ := κ) (World.init members) := by
  intro X U lg h; simp [World.init] at h

theorem electedIsLeaderLog_step {members : List Nat} {w w' : World σ κ}
    (h : ElectedIsLeaderLog w) (hs : Step members w w') : ElectedIsLeaderLog w' := by
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev → ElectedIsLeaderLog w' := by
    intro j ev hw
    subst hw
    intro X U lg hmem
    rw [act_leaderLogs]
    rcases List.mem_append.mp hmem with h' | h'
    · exact List.mem_append_left _ (h X U lg h')
    · obtain ⟨h1, h2, h3, h4, _⟩ := mem_electedOf h'
      subst h1; subst h2; subst h3
      exact List.mem_append_right _ (leaderLogOf_self h4)
  cases hs with
  | deliver s d m hd hm => exact key d _ rfl
  | electionTimeout k hk => exact key k _ rfl
  | heartbeat k hk => exact key k _ rfl
  | client k rid cmd hk => exact key k _ rfl

theorem electedIsLeaderLog_reachable {members : List Nat} {w : World σ κ}
    (h : Reachable members w) : ElectedIsLeaderLog w := by
  induction h with
  | init => exact electedIsLeaderLog_init members
  | tail _ hs ih => exact electedIsLeaderLog_step ih hs

/-! ## The induction on the term -/

/--
**The Figure-9 induction.**

Every leader log of a term later than a commit's already contains the committed
prefix. The induction is on the term: the new leader's election quorum meets the
commit's acknowledgement quorum at some node `x`, attribution tells us where
`x`'s log came from — a leader of a term in `[T, tY)` — and the induction
hypothesis carries the prefix from there onto `x`, then domination carries it
onto the new leader.
-/
theorem lc_aux {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w)
    {L T c : Nat} {lgL : σ}
    (hL : (L, T, lgL) ∈ w.leaderLogs)
    (hcT : LogStore.termAt lgL c = some T)
    (hack : AckQuorum members w T c) :
    ∀ (n Y tY : Nat) (lgY : σ), (Y, tY, lgY) ∈ w.leaderLogs → T < tY → tY ≤ n →
      AgreeUpTo lgY lgL c := by
  have hwfL : WellFormedLog w lgL := leaderLogWF_reachable hnd hrch L T lgL hL
  obtain ⟨ec, hec⟩ : ∃ ec, LogStore.get lgL c = some ec := by
    unfold LogStore.termAt at hcT
    cases hq : LogStore.get lgL c with
    | none => rw [hq] at hcT; simp at hcT
    | some ec => exact ⟨ec, rfl⟩
  have hcL : c ≤ LogStore.lastIndex lgL :=
    ((LogStore.get_isSome_iff lgL c).mp (by rw [hec]; rfl)).2
  have hLled : (L, T) ∈ w.led := (llInv_reachable hnd hrch).led L T lgL hL
  obtain ⟨Q, hQ1, hQ2, hQ3, hQ4⟩ := hack
  intro n
  induction n with
  | zero => intro Y tY lgY _ h1 h2; omega
  | succ n ih =>
    intro Y tY lgY hY htY hle
    obtain ⟨lgel, hel, hpre⟩ := leaderLogHasElected_reachable hnd hrch Y tY lgY hY
    obtain ⟨V, hV1, hV2, hV3, hV4⟩ := electedQuorum_reachable hnd hrch Y tY lgel hel
    obtain ⟨x, hxV, hxQ⟩ :=
      quorum_intersect (c := { me := 0, members := members }) hnd
        ⟨hV1, hV2, hV3⟩ ⟨hQ1, hQ2, hQ3⟩
    obtain ⟨m, lgx, hxack, hcm⟩ := hQ4 x hxQ
    -- attribution turns a per-index witness into agreement up to `c`
    have hwit : ∀ (lgw : σ), (∀ k, k ≤ m → ∃ (X tX : Nat) (lgX : σ),
          (X, tX, lgX) ∈ w.leaderLogs ∧ T ≤ tX ∧ tX < tY
            ∧ (T = tX → k ≤ LogStore.lastIndex lgX)
            ∧ LogStore.get lgw k = LogStore.get lgX k) → AgreeUpTo lgw lgL c := by
      intro lgw hw k hk
      obtain ⟨X, tX, lgX, h1, h2, h3, h5, h4⟩ := hw k (by omega)
      rcases Nat.eq_or_lt_of_le h2 with heq | hlt
      · -- the commit's own leader: two snapshots of one term form a chain
        subst heq
        have hXled : (X, T) ∈ w.led := (llInv_reachable hnd hrch).led X T lgX h1
        have hXL : X = L := led_unique hnd hrch hXled hLled
        subst hXL
        rcases (llInv_reachable hnd hrch).chain X T lgX lgL h1 hL with hp | hp
        · rw [h4, ← hp k (h5 rfl)]
        · rw [h4, hp k (by omega)]
      · -- a later leader: the induction hypothesis already carries the prefix
        rw [h4]
        exact ih X tX lgX h1 hlt (by omega) k hk
    have hwfel : WellFormedLog w lgel := (snapWF_reachable hnd hrch).2.2 Y tY lgel hel
    have hgoal : AgreeUpTo lgel lgL c := by
      rcases hV4 x hxV with hxY | hgrant
      · -- the intersecting node is the new leader itself
        subst hxY
        exact hwit lgel (fun k hk =>
          electedAttributed_reachable hnd hrch x T m lgx hxack tY lgel hel htY k hk)
      · -- a genuine grant from another node
        obtain ⟨lgv, hlgv⟩ := grantHasVoteLog_reachable hrch x Y tY hgrant
        have hvote : (x, Y, tY) ∈ w.votes :=
          (allInv_reachable hrch).ghost.recorded x Y tY hgrant
        have hv : AgreeUpTo lgv lgL c := hwit lgv (fun k hk =>
          voteAttributed_reachable hnd hrch x T m lgx hxack tY lgv hlgv htY k hk)
        have hwfv : WellFormedLog w lgv := voteLogWF_reachable hnd hrch x tY lgv hlgv
        have hdom := vote_dominates hnd hrch hlgv hvote hel
        have hlt : LogStore.lastTerm lgel < tY := electedTermLt_reachable hnd hrch Y tY lgel hel
        exact dominate_carries hnd hrch hwfv hwfel hwfL hcT hv hdom
          (N := n) (by omega) (fun Y' tY' lgY' h1 h2 h3 => ih Y' tY' lgY' h1 h2 h3)
    -- the snapshot extends the elected log, so it inherits the agreement
    intro k hk
    have hcel : LogStore.get lgel c = some ec := by rw [hgoal c (Nat.le_refl _)]; exact hec
    have hclen : c ≤ LogStore.lastIndex lgel :=
      ((LogStore.get_isSome_iff lgel c).mp (by rw [hcel]; rfl)).2
    rw [hpre k (by omega)]
    exact hgoal k hk

/--
**Leader Completeness.**

An entry committed in term `T` appears, at the same index, in the log of every
leader elected in a later term.
-/
theorem leaderCompleteness {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) : Protocol.LeaderCompleteness w := by
  intro idx e T U Y lgel hcom hel hTU
  obtain ⟨L, c, lgL, Q, hc, hidx, hgete⟩ := hcom
  obtain ⟨hcT, hLmem⟩ := commit_ack_quorum hnd hrch hc
  obtain ⟨hQ1, hQ2, hQ3, hQ4⟩ := commitQuorum_reachable hnd hrch L T c lgL Q hc
  have hagree : AgreeUpTo lgel lgL c :=
    lc_aux hnd hrch hLmem hcT ⟨Q, hQ1, hQ2, hQ3, hQ4⟩ U Y U lgel
      (electedIsLeaderLog_reachable hrch Y U lgel hel) hTU (Nat.le_refl _)
  rw [hagree idx hidx]; exact hgete

end RaftKV.Proof
