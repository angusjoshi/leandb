import RaftKV.Proof.MsgLeader

/-!
# Change attribution

The invariant that breaks the circularity in Leader Completeness.

Every earlier attempt needed to know that a node which acknowledged a prefix
*still holds it later*, and every proof of that needed Leader Completeness
itself. The way out is to stop asking whether the node kept the prefix and ask
instead **where its current contents came from**:

> Wherever a node's log now stands, at every index it once acknowledged, it
> agrees with some recorded leader log of a term between the acknowledgement's
> term and the node's own current term.

That statement mentions no commit and no quorum, so it is provable outright. The
term bound is what makes the eventual induction well-founded: a node's log can
only have been reshaped by leaders it had already caught up to.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [LawfulLogStore σ] [KVStore κ]

/-- A node's log, at any index it acknowledged, mirrors some leader log of a term in range. -/
def ChangeAttributed (w : World σ κ) : Prop :=
  ∀ (v T m : Nat) (lgp : σ), (v, T, m, lgp) ∈ w.acks → ∀ k, k ≤ m →
    ∃ (X tX : Nat) (lgX : σ), (X, tX, lgX) ∈ w.leaderLogs ∧ T ≤ tX
      ∧ tX ≤ (w.nodes v).currentTerm
      ∧ (T = tX → k ≤ LogStore.lastIndex lgX)
      ∧ (tX = (w.nodes v).currentTerm → (w.nodes v).votedFor ≠ none)
      ∧ LogStore.get (w.nodes v).log k = LogStore.get lgX k

theorem changeAttributed_init (members : List Nat) :
    ChangeAttributed (σ := σ) (κ := κ) (World.init members) := by
  intro v T m lgp h; simp [World.init] at h

/-- The acknowledger's own term is at least the term it acknowledged in. -/
theorem ack_term_le {members : List Nat} {w : World σ κ}
    (hrch : Reachable members w) {v T m : Nat} {lgp : σ}
    (h : (v, T, m, lgp) ∈ w.acks) : T ≤ (w.nodes v).currentTerm := by
  -- the acknowledgement carried the node's own term at the time
  induction hrch with
  | init => simp [World.init] at h
  | @tail w0 w1 hr hs ih =>
      have key : ∀ (j : Nat) (ev : Event), w1 = w0.act j ev → T ≤ (w1.nodes v).currentTerm := by
        intro j ev hw
        subst hw
        rcases List.mem_append.mp h with h' | h'
        · exact Nat.le_trans (ih h') (act_term_mono w0 j ev v)
        · rcases mem_ackOf_cases h' with ⟨to0, hact, hvj, _⟩ | ⟨_, hvj, hT, _, _⟩
          case inr =>
            subst hvj; rw [act_nodes_self, hT]
            exact Nat.le_refl _
          subst hvj
          rw [act_nodes_self]
          -- the response carries the responder's post-state term
          obtain ⟨src, l, pi, pt, es, lc, hev, _, _, _, _, hle, _⟩ := step_ack_shape hact
          subst hev
          rw [Protocol.step, handleAppendEntries_term_eq]
          omega
      cases hs with
      | deliver s d m0 hd hm => exact key d _ rfl
      | electionTimeout k hk => exact key k _ rfl
      | heartbeat k hk => exact key k _ rfl
      | client k rid cmd hk => exact key k _ rfl
      | crash k hk =>
          by_cases hvk : v = k
          · subst hvk; rw [crash_nodes_self, restart_currentTerm]
            exact ih (by rwa [crash_acks] at h)
          · rw [crash_nodes_ne _ _ hvk]; exact ih (by rwa [crash_acks] at h)

/-- A freshly recorded acknowledgement carries the node's post-state term. -/
theorem fresh_ack_term {w : World σ κ} {v T m : Nat} {lgp : σ} {ev : Event}
    (h : (v, T, m, lgp) ∈ ackOf v (Protocol.step (w.nodes v) ev).1 (fullStep (w.nodes v) (w.full v) ev)
            (Protocol.step (w.nodes v) ev).2) :
    ((w.act v ev).nodes v).currentTerm = T := by
  rw [act_nodes_self]
  rcases mem_ackOf_cases h with ⟨to0, hact, _, _⟩ | ⟨_, _, hT, _, _⟩
  · obtain ⟨src, l, pi, pt, es, lc, hev, _, _, _, _, hle, _⟩ := step_ack_shape hact
    subst hev
    rw [Protocol.step, handleAppendEntries_term_eq]
    omega
  · exact hT.symm

/-- A node that records an acknowledgement has spent its vote for that term. -/
theorem fresh_ack_voted {members : List Nat} {w : World σ κ}
    {v T m : Nat} {lgp : σ} {ev : Event} (hr' : Reachable members (w.act v ev))
    (h : (v, T, m, lgp) ∈ ackOf v (Protocol.step (w.nodes v) ev).1 (fullStep (w.nodes v) (w.full v) ev)
            (Protocol.step (w.nodes v) ev).2) :
    ((w.act v ev).nodes v).votedFor ≠ none := by
  rcases mem_ackOf_cases h with ⟨to0, hact, _, _⟩ | ⟨hlead, _, _, _, _⟩
  · obtain ⟨src, l, pi, pt, es, lc, hev, _, _, _, _, hle, _⟩ := step_ack_shape hact
    subst hev
    rw [act_nodes_self, Protocol.step]
    exact handleAppendEntries_votedFor_ne _ _ _ _ _ _ _ _ hle
  · have hv := ((allInv_reachable hr').leader.votes v
      (by rw [act_nodes_self, hlead]; exact fun hq => Role.noConfusion hq)).1
    rw [hv]; simp

/-! ## Holding an acknowledged prefix within its term -/

/--
**A node that acknowledged a prefix still holds it while its term stands.**

Within one term the leader is unique and its log only grows, so any payload the
node receives while still in term `T` either extends what it already agreed
with, or matches it entry for entry and therefore changes nothing. The bound to
a single term is what makes this provable outright: it needs no claim about
later leaders, and it is exactly the input the attribution invariant lacks at
the moment a node's term moves on.
-/
def AckHold (w : World σ κ) : Prop :=
  ∀ (v T m : Nat) (lgp : σ), (v, T, m, lgp) ∈ w.acks → T = (w.nodes v).currentTerm →
    ∃ (L : Nat) (lgL : σ), (L, T, lgL) ∈ w.leaderLogs ∧ m ≤ LogStore.lastIndex lgL
      ∧ ∀ k, k ≤ m → LogStore.get (w.nodes v).log k = LogStore.get lgL k

theorem ackHold_init (members : List Nat) :
    AckHold (σ := σ) (κ := κ) (World.init members) := by
  intro v T m lgp h; simp [World.init] at h

/-- **`AckHold` is preserved by every step.** -/
theorem ackHold_step {members : List Nat} {w w' : World σ κ}
    (hnd : members.Nodup) (hr : Reachable members w)
    (h : AckHold w) (hs : Step members w w') : AckHold w' := by
  have hr' : Reachable members w' := Reachable.tail hr hs
  have hmsg := msgFromLeaderLog_reachable hr
  have hack' := ackAgrees_reachable hnd hr'
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev →
      (∀ src m', ev = Event.recv src m' → (src, j, m') ∈ w.sent) → AckHold w' := by
    intro j ev hw hdel
    subst hw
    intro v T m lgp hmem hT
    rcases List.mem_append.mp hmem with h' | h'
    · -- an older acknowledgement
      by_cases hvj : v = j
      · subst hvj
        have hpre : T = (w.nodes v).currentTerm := by
          have h1 := ack_term_le hr h'
          have h2 := act_term_mono w v ev v
          rw [act_nodes_self] at hT h2
          omega
        obtain ⟨L, lgL, hL1, hL2, hL3⟩ := h v T m lgp h' hpre
        rw [act_nodes_self]
        rcases step_log (w.nodes v) ev with hl | ⟨rid, cmd, hev, hl⟩ |
          ⟨src, term, l, pi, pt, es, lc, hev, hl, hpi, hchk, _, hct⟩
        · exact ⟨L, lgL, leaderLog_mono hL1, hL2, by rw [hl]; exact hL3⟩
        · -- a client append never disturbs what is already there
          refine ⟨L, lgL, leaderLog_mono hL1, hL2, ?_⟩
          intro k hk
          have hne : k ≠ LogStore.lastIndex (w.nodes v).log + 1 := by
            intro hc
            have hnone : LogStore.get (w.nodes v).log k = none := by
              cases hq : LogStore.get (w.nodes v).log k with
              | none => rfl
              | some z =>
                  exfalso
                  have := ((LogStore.get_isSome_iff (w.nodes v).log k).mp (by rw [hq]; rfl)).2
                  omega
            have hsome : (LogStore.get lgL k).isSome :=
              (LogStore.get_isSome_iff lgL k).mpr ⟨by omega, by omega⟩
            rw [← hL3 k hk, hnone] at hsome
            exact Bool.noConfusion hsome
          rw [hl, LogStore.get_append, if_neg hne]
          exact hL3 k hk
        · -- a splice, necessarily from this very term's leader
          subst hev
          have hterm : term = T := by
            rw [act_nodes_self, Protocol.step, handleAppendEntries_term_eq] at hT
            omega
          subst hterm
          have hpkt := hdel src (Msg.appendEntries term l pi pt es lc) rfl
          obtain ⟨lgS, hS1, hS2, hS3, hS4⟩ := hmsg src v term l pi pt es lc hpkt
          have hwfV : WellFormedLog w (w.nodes v).log := wf_node hnd hr v
          have hpre' : pi ≤ LogStore.lastIndex lgS := prev_reach hr hwfV hchk hS3
          have hlast : pi + es.length = LogStore.lastIndex lgS := by omega
          -- the sender leads this term, so it is the very leader already on record
          have hsrcL : L = src := by
            have h1 := (llInv_reachable hnd hr).led src term lgS hS1
            have h2 := (llInv_reachable hnd hr).led L term lgL hL1
            exact led_unique hnd hr h2 h1
          subst hsrcL
          have hchain := (llInv_reachable hnd hr).chain L term lgS lgL hS1 hL1
          rcases Nat.lt_or_ge (LogStore.lastIndex lgS) m with hshort | hlong
          · -- the payload is already there: nothing changes
            have hid : appendFrom (w.nodes v).log (pi + 1) es = (w.nodes v).log := by
              refine appendFrom_id_of_match es (w.nodes v).log (pi + 1) ?_
              intro n e hn
              have hlt : pi + 1 + n ≤ LogStore.lastIndex lgS := by
                have : n < es.length := by
                  rcases Nat.lt_or_ge n es.length with hq | hq
                  · exact hq
                  · exact absurd hn (by rw [List.getElem?_eq_none hq]; simp)
                omega
              have hSk : LogStore.get lgS (pi + 1 + n) = some e := hS2 n e hn
              have hLk : LogStore.get lgL (pi + 1 + n) = some e := by
                rcases hchain with hp | hp
                · rw [hp (pi + 1 + n) hlt]; exact hSk
                · rw [← hSk]; exact (hp (pi + 1 + n) (by omega)).symm
              refine ⟨e, ?_, rfl⟩
              rw [hL3 (pi + 1 + n) (by omega)]; exact hLk
            exact ⟨L, lgL, leaderLog_mono hL1, hL2, by rw [hl, hid]; exact hL3⟩
          · -- the payload reaches past what was acknowledged: switch to the sender's log
            refine ⟨L, lgS, leaderLog_mono hS1, by omega, ?_⟩
            have hwfS : WellFormedLog w lgS := leaderLogWF_reachable hnd hr L term lgS hS1
            have hwfNew : WellFormedLog (w.act v (Event.recv L
                (Msg.appendEntries term l pi pt es lc)))
                (appendFrom (w.nodes v).log (pi + 1) es) := by
              have h0 := wf_node hnd hr' v
              rw [act_nodes_self] at h0
              exact hl ▸ h0
            intro k hk
            rw [hl]
            exact splice_agrees hnd hr' hwfV.mono hwfS.mono hpi hchk hS3 hS2 hwfNew k (by omega)
      · rw [act_nodes_ne _ _ _ hvj] at hT ⊢
        obtain ⟨L, lgL, hL1, hL2, hL3⟩ := h v T m lgp h' hT
        exact ⟨L, lgL, leaderLog_mono hL1, hL2, hL3⟩
    · -- the acknowledgement made by this very step
      obtain ⟨hvj, hlg⟩ := mem_ackOf h'
      subst hvj
      obtain ⟨_, L, lgL, hL1, hL2, hL3⟩ := hack' v T m lgp (List.mem_append_right _ h')
      refine ⟨L, lgL, hL1, hL2, ?_⟩
      have hq : ((w.act v ev).nodes v).log = lgp := by
        rw [act_nodes_self]; exact hlg.symm
      rw [hq]; exact hL3
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
      intro v T m lgp hm hT
      rw [crash_acks] at hm
      by_cases hvk : v = k
      · subst hvk
        rw [crash_nodes_self, restart_currentTerm] at hT
        rw [crash_nodes_self, restart_log]
        obtain ⟨L, lgL, h1, h2, h3⟩ := h v T m lgp hm hT
        exact ⟨L, lgL, by rw [crash_leaderLogs]; exact h1, h2, h3⟩
      · rw [crash_nodes_ne _ _ hvk] at hT ⊢
        obtain ⟨L, lgL, h1, h2, h3⟩ := h v T m lgp hm hT
        exact ⟨L, lgL, by rw [crash_leaderLogs]; exact h1, h2, h3⟩

/-- **An acknowledged prefix is held for as long as its term stands.** -/
theorem ackHold_reachable {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) : AckHold w := by
  induction h with
  | init => exact ackHold_init members
  | tail hr hs ih => exact ackHold_step hnd hr ih hs

/--
**A spent vote stays spent while the term stands.**

The side condition of the attribution invariant only bites in the node's own
current term, and a node that has voted in a term cannot un-vote without leaving
the term. So the condition survives any step that does not advance the term, and
is vacuous for any step that does.
-/
theorem voted_carry (w : World σ κ) (j : Nat) (ev : Event) {v tX : Nat}
    (h3 : tX ≤ (w.nodes v).currentTerm)
    (hV : tX = (w.nodes v).currentTerm → (w.nodes v).votedFor ≠ none) :
    tX = ((w.act j ev).nodes v).currentTerm → ((w.act j ev).nodes v).votedFor ≠ none := by
  intro heq
  have hmono := act_term_mono w j ev v
  have hEq : tX = (w.nodes v).currentTerm := by omega
  have hpre := hV hEq
  obtain ⟨c, hc⟩ : ∃ c, (w.nodes v).votedFor = some c := by
    cases hq : (w.nodes v).votedFor with
    | none => exact absurd hq hpre
    | some c => exact ⟨c, rfl⟩
  by_cases hvj : v = j
  · subst hvj
    rw [act_nodes_self] at heq ⊢
    rcases votedFor_step (w.nodes v) ev c hc with hq | hq
    · rw [hq]; simp
    · omega
  · rw [act_nodes_ne _ _ _ hvj, hc]; simp

/-- **Change attribution is preserved by every step.** -/
theorem changeAttributed_step {members : List Nat} {w w' : World σ κ}
    (hnd : members.Nodup) (hr : Reachable members w)
    (h : ChangeAttributed w) (hs : Step members w w') : ChangeAttributed w' := by
  have hr' : Reachable members w' := Reachable.tail hr hs
  have hmsg := msgFromLeaderLog_reachable hr
  have hack' := ackAgrees_reachable hnd hr'
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev →
      (∀ src m', ev = Event.recv src m' → (src, j, m') ∈ w.sent) →
      ChangeAttributed w' := by
    intro j ev hw hdel
    subst hw
    intro v T m lgp hmem k hk
    -- the acknowledgement is either old or the one this step just made
    have holdcase : (v, T, m, lgp) ∈ w.acks →
        ∃ (X tX : Nat) (lgX : σ), (X, tX, lgX) ∈ (w.act j ev).leaderLogs ∧ T ≤ tX
          ∧ tX ≤ ((w.act j ev).nodes v).currentTerm
          ∧ (T = tX → k ≤ LogStore.lastIndex lgX)
          ∧ (tX = ((w.act j ev).nodes v).currentTerm →
              ((w.act j ev).nodes v).votedFor ≠ none)
          ∧ LogStore.get ((w.act j ev).nodes v).log k = LogStore.get lgX k := by
      intro hold
      obtain ⟨X, tX, lgX, hX1, hX2, hX3, hX5, hX6, hX4⟩ := h v T m lgp hold k hk
      have hcarry := voted_carry w j ev hX3 hX6
      by_cases hvj : v = j
      · subst hvj
        rw [act_nodes_self]
        have hmono := act_term_mono w v ev v
        rw [act_nodes_self] at hmono
        rcases step_log (w.nodes v) ev with hl | ⟨rid, cmd, hev, hl⟩ |
          ⟨src, term, l, pi, pt, es, lc, hev, hl, hpi, hchk, _, hct⟩
        · exact ⟨X, tX, lgX, leaderLog_mono hX1, hX2, by omega, hX5,
            by rw [act_nodes_self] at hcarry; exact hcarry, by rw [hl]; exact hX4⟩
        · -- a client append: only the new top index differs
          by_cases hktop : k = LogStore.lastIndex (w.nodes v).log + 1
          · have hlead : (Protocol.step (w.nodes v) ev).1.role = Role.leader := by
              subst hev
              have hpre : (w.nodes v).role = Role.leader := by
                rcases Classical.em ((w.nodes v).role = Role.leader) with hc | hc
                · exact hc
                · exfalso
                  rw [Protocol.step, handleClientReq, if_pos (by simp [hc])] at hl
                  have := congrArg LogStore.lastIndex hl
                  simp only [LogStore.lastIndex_append] at this
                  omega
              rw [Protocol.step, handleClientReq, if_neg (by rw [hpre]; simp)]
              dsimp only; simp [hpre]
            refine ⟨v, (Protocol.step (w.nodes v) ev).1.currentTerm,
              (Protocol.step (w.nodes v) ev).1.log, ?_, by omega, Nat.le_refl _, ?_, ?_, rfl⟩
            · rw [act_leaderLogs]
              exact List.mem_append_right _ (leaderLogOf_self hlead)
            · intro _
              rw [hl, LogStore.lastIndex_append]; omega
            · intro _
              have := ((allInv_reachable hr').leader.votes v
                (by rw [act_nodes_self, hlead]; exact fun hq => Role.noConfusion hq)).1
              rw [act_nodes_self] at this
              rw [this]; simp
          · refine ⟨X, tX, lgX, leaderLog_mono hX1, hX2, by omega, hX5,
              by rw [act_nodes_self] at hcarry; exact hcarry, ?_⟩
            rw [hl, LogStore.get_append, if_neg hktop]
            exact hX4
        · -- a splice: attribute to the sender, or note nothing changed
          subst hev
          have hpkt := hdel src (Msg.appendEntries term l pi pt es lc) rfl
          obtain ⟨lgS, hS1, hS2, hS3, hS4⟩ := hmsg src v term l pi pt es lc hpkt
          have hbound : pi + 1 ≤ LogStore.lastIndex (w.nodes v).log + 1 := by omega
          have hmax : LogStore.lastIndex lgS ≤ pi + es.length := by omega
          have htT : T ≤ term := by
            have := ack_term_le hr hold
            omega
          by_cases hkm : k ≤ pi + es.length
          · -- inside what the sender sent: the fresh acknowledgement pins it down
            have hwfV : WellFormedLog w (w.nodes v).log := wf_node hnd hr v
            have hwfS : WellFormedLog w lgS :=
              leaderLogWF_reachable hnd hr src term lgS hS1
            have hwfNew : WellFormedLog (w.act v (Event.recv src
                (Msg.appendEntries term l pi pt es lc)))
                (appendFrom (w.nodes v).log (pi + 1) es) := by
              have h0 := wf_node hnd hr' v
              rw [act_nodes_self] at h0
              exact hl ▸ h0
            have hpre' : pi ≤ LogStore.lastIndex lgS := prev_reach hr hwfV hchk hS3
            refine ⟨src, term, lgS, leaderLog_mono hS1, htT, by
              rw [Protocol.step, handleAppendEntries_term_eq]; omega,
              fun _ => by omega, ?_, ?_⟩
            · intro _
              rw [Protocol.step]
              exact handleAppendEntries_votedFor_ne _ _ _ _ _ _ _ _ hct
            · rw [hl]
              exact splice_agrees hnd hr' hwfV.mono hwfS.mono hpi hchk hS3 hS2 hwfNew k hkm
          · -- beyond it: either nothing changed, or the log ends where the sender's does
            by_cases hsome : (LogStore.get (Protocol.step (w.nodes v) (Event.recv src
                (Msg.appendEntries term l pi pt es lc))).1.log k).isSome
            · have hun := appendFrom_above_unchanged es (w.nodes v).log (pi + 1) k hbound
                (by omega) (by omega) (by rw [← hl]; exact hsome)
              refine ⟨X, tX, lgX, leaderLog_mono hX1, hX2, by omega, hX5,
                by rw [act_nodes_self] at hcarry; exact hcarry, ?_⟩
              rw [hl, hun k]
              exact hX4
            · refine ⟨src, term, lgS, leaderLog_mono hS1, htT, by
                rw [Protocol.step, handleAppendEntries_term_eq]; omega, ?_, ?_, ?_⟩
              · -- the acknowledged prefix is still held, so this branch cannot arise
                intro hTt
                exfalso
                have hTterm : T = ((w.act v (Event.recv src
                    (Msg.appendEntries term l pi pt es lc))).nodes v).currentTerm := by
                  rw [act_nodes_self, Protocol.step, handleAppendEntries_term_eq]
                  omega
                obtain ⟨L0, lg0, _, hr0, ha0⟩ :=
                  ackHold_reachable hnd hr' v T m lgp (List.mem_append_left _ hold) hTterm
                have hk1 : 1 ≤ k := by
                  rcases Nat.eq_zero_or_pos k with h0 | h0
                  · exfalso
                    have := hS4
                    have hz : LogStore.lastIndex lgS ≤ pi + es.length := by omega
                    omega
                  · exact h0
                have hsome' : (LogStore.get lg0 k).isSome :=
                  (LogStore.get_isSome_iff lg0 k).mpr ⟨hk1, by omega⟩
                rw [← ha0 k hk, act_nodes_self] at hsome'
                exact hsome hsome'
              · intro _
                rw [Protocol.step]
                exact handleAppendEntries_votedFor_ne _ _ _ _ _ _ _ _ hct
              have h1 : LogStore.get (Protocol.step (w.nodes v) (Event.recv src
                  (Msg.appendEntries term l pi pt es lc))).1.log k = none := by
                cases hq : LogStore.get (Protocol.step (w.nodes v) (Event.recv src
                    (Msg.appendEntries term l pi pt es lc))).1.log k with
                | none => rfl
                | some z => exfalso; rw [hq] at hsome; exact hsome rfl
              have h2 : LogStore.get lgS k = none := by
                cases hq : LogStore.get lgS k with
                | none => rfl
                | some z =>
                    exfalso
                    have := ((LogStore.get_isSome_iff lgS k).mp (by rw [hq]; rfl)).2
                    omega
              rw [h1, h2]
      · rw [act_nodes_ne _ _ _ hvj] at hcarry ⊢
        exact ⟨X, tX, lgX, leaderLog_mono hX1, hX2, hX3, hX5, hcarry, hX4⟩
    rcases List.mem_append.mp hmem with h' | h'
    · exact holdcase h'
    · -- the acknowledgement made by this very step
      obtain ⟨hvj, hlg⟩ := mem_ackOf h'
      subst hvj
      obtain ⟨_, L', lgL', hL1, hLr, hL2⟩ := hack' v T m lgp (List.mem_append_right _ h')
      refine ⟨L', T, lgL', hL1, Nat.le_refl _,
        ack_term_le hr' (List.mem_append_right _ h'), fun _ => by omega, ?_, ?_⟩
      · -- the acknowledgement came of accepting a leader's payload, or the node leads
        intro _
        exact fresh_ack_voted hr' h'
      · have hq : ((w.act v ev).nodes v).log = lgp := by
          rw [act_nodes_self]; exact hlg.symm
        rw [hq]
        exact hL2 k hk
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
      intro v T m lgp hm k' hk'
      rw [crash_acks] at hm
      by_cases hvk : v = k
      · subst hvk
        rw [crash_nodes_self, restart_currentTerm, restart_votedFor, restart_log]
        obtain ⟨X, tX, lgX, h1, h2, h3, h5, h6, h4⟩ := h v T m lgp hm k' hk'
        exact ⟨X, tX, lgX, by rw [crash_leaderLogs]; exact h1, h2, h3, h5, h6, h4⟩
      · rw [crash_nodes_ne _ _ hvk]
        obtain ⟨X, tX, lgX, h1, h2, h3, h5, h6, h4⟩ := h v T m lgp hm k' hk'
        exact ⟨X, tX, lgX, by rw [crash_leaderLogs]; exact h1, h2, h3, h5, h6, h4⟩

/-- **Change attribution holds in every reachable world.** -/
theorem changeAttributed_reachable {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) : ChangeAttributed w := by
  induction h with
  | init => exact changeAttributed_init members
  | tail hr hs ih => exact changeAttributed_step hnd hr ih hs

/-! ## Vote-time attribution -/

/-- A vote record's term never exceeds the voter's current term. -/
def VoteTermLe (w : World σ κ) : Prop :=
  ∀ (v U : Nat) (lgv : σ), (v, U, lgv) ∈ w.voteLogs → U ≤ (w.nodes v).currentTerm

theorem voteTermLe_init (members : List Nat) :
    VoteTermLe (σ := σ) (κ := κ) (World.init members) := by
  intro v U lgv h; simp [World.init] at h

theorem voteTermLe_step {members : List Nat} {w w' : World σ κ}
    (h : VoteTermLe w) (hs : Step members w w') : VoteTermLe w' := by
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev → VoteTermLe w' := by
    intro j ev hw
    subst hw
    intro v U lgv hmem
    rw [act_voteLogs] at hmem
    rcases List.mem_append.mp hmem with h' | h'
    · exact Nat.le_trans (h v U lgv h') (act_term_mono w j ev v)
    · -- a fresh grant carries the voter's own term
      unfold voteLogOf at h'
      rcases List.mem_filterMap.mp h' with ⟨a, ha, heq⟩
      cases a with
      | reply _ _ _ => simp at heq
      | notLeader _ _ => simp at heq
      | send to msg =>
          cases msg with
          | requestVote a b c d => simp at heq
          | appendEntries a b c d e f => simp at heq
          | appendEntriesResp a b c => simp at heq
          | requestVoteResp t g =>
              cases g with
              | false => simp at heq
              | true =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at heq
                  obtain ⟨hv, hU, _⟩ := heq
                  subst hv; subst hU
                  rw [act_nodes_self]
                  rcases grant_only_from_requestVote ha with ⟨src, term, cd, li, lt, hev⟩
                  subst hev
                  rw [Protocol.step] at ha
                  obtain ⟨_, h2, _, _, _⟩ := handleRequestVote_grant ha
                  rw [Protocol.step]
                  omega
  cases hs with
  | deliver s d m0 hd hm => exact key d _ rfl
  | electionTimeout k hk => exact key k _ rfl
  | heartbeat k hk => exact key k _ rfl
  | client k rid cmd hk => exact key k _ rfl
  | crash k hk =>
      intro v U lgv hm
      rw [crash_voteLogs] at hm
      by_cases hvk : v = k
      · subst hvk; rw [crash_nodes_self, restart_currentTerm]; exact h v U lgv hm
      · rw [crash_nodes_ne _ _ hvk]; exact h v U lgv hm

theorem voteTermLe_reachable {members : List Nat} {w : World σ κ} (h : Reachable members w) :
    VoteTermLe w := by
  induction h with
  | init => exact voteTermLe_init members
  | tail _ hs ih => exact voteTermLe_step ih hs

/--
**Attribution at vote time.**

The same statement as `ChangeAttributed`, but about the log a voter held when it
voted — which is the log the `upToDate` check actually compared against.
-/
def VoteAttributed (w : World σ κ) : Prop :=
  ∀ (v T m : Nat) (lgp : σ), (v, T, m, lgp) ∈ w.acks →
    ∀ (U : Nat) (lgv : σ), (v, U, lgv) ∈ w.voteLogs → T < U → ∀ k, k ≤ m →
      ∃ (X tX : Nat) (lgX : σ), (X, tX, lgX) ∈ w.leaderLogs ∧ T ≤ tX ∧ tX < U
        ∧ (T = tX → k ≤ LogStore.lastIndex lgX)
        ∧ LogStore.get lgv k = LogStore.get lgX k

theorem voteAttributed_init (members : List Nat) :
    VoteAttributed (σ := σ) (κ := κ) (World.init members) := by
  intro v T m lgp h; simp [World.init] at h

/-- **Vote-time attribution is preserved by every step.** -/
theorem voteAttributed_step {members : List Nat} {w w' : World σ κ}
    (hnd : members.Nodup) (hr : Reachable members w)
    (h : VoteAttributed w) (hs : Step members w w') : VoteAttributed w' := by
  have hr' : Reachable members w' := Reachable.tail hr hs
  have hca := changeAttributed_reachable hnd hr
  have hvt := voteTermLe_reachable hr
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev → VoteAttributed w' := by
    intro j ev hw
    subst hw
    intro v T m lgp hack U lgv hvote hTU k hk
    rcases List.mem_append.mp hvote with hv' | hv'
    · rcases List.mem_append.mp hack with ha' | ha'
      · obtain ⟨X, tX, lgX, h1, h2, h3, h5, h4⟩ := h v T m lgp ha' U lgv hv' hTU k hk
        exact ⟨X, tX, lgX, leaderLog_mono h1, h2, h3, h5, h4⟩
      · -- a fresh acknowledgement cannot predate an older vote of a higher term
        exfalso
        obtain ⟨hvj, _⟩ := mem_ackOf ha'
        subst hvj
        have hUle := hvt v U lgv hv'
        -- the acknowledgement is made at the node's own current term
        have hcur : ((w.act v ev).nodes v).currentTerm = T := fresh_ack_term ha'
        have hmono := act_term_mono w v ev v
        omega
    · -- a fresh vote: the voter's current log is what was compared
      obtain ⟨to1, hgact, hvj, hlgeq⟩ :
          ∃ to1, Action.send to1 (Msg.requestVoteResp U true)
              ∈ (Protocol.step (w.nodes j) ev).2
            ∧ v = j ∧ lgv = (Protocol.step (w.nodes j) ev).1.log := by
        unfold voteLogOf at hv'
        rcases List.mem_filterMap.mp hv' with ⟨a, ha, heq⟩
        cases a with
        | reply _ _ _ => simp at heq
        | notLeader _ _ => simp at heq
        | send to msg =>
            cases msg with
            | requestVote a b c d => simp at heq
            | appendEntries a b c d e f => simp at heq
            | appendEntriesResp a b c => simp at heq
            | requestVoteResp t g =>
                cases g with
                | false => simp at heq
                | true =>
                    simp only [Option.some.injEq, Prod.mk.injEq] at heq
                    exact ⟨to, by rw [← heq.2.1]; exact ha, heq.1.symm, heq.2.2.symm⟩
      subst hvj
      -- the grant leaves the log alone and stamps the voter's own term
      obtain ⟨s1, t1, c1, li1, lt1, hev1⟩ := grant_only_from_requestVote hgact
      have hUeq : U = (Protocol.step (w.nodes v) ev).1.currentTerm := by
        rw [hev1] at hgact ⊢
        rw [Protocol.step] at hgact
        obtain ⟨_, h2, _, _, _⟩ := handleRequestVote_grant hgact
        rw [Protocol.step]; exact h2.symm
      have hlogsame : (Protocol.step (w.nodes v) ev).1.log = (w.nodes v).log := by
        rw [hev1]
        rcases step_log (w.nodes v) (Event.recv s1 (Msg.requestVote t1 c1 li1 lt1)) with
          hl | ⟨_, _, he, _⟩ | ⟨_, _, _, _, _, _, _, he, _⟩
        · exact hl
        · exact absurd he (by simp)
        · exact absurd he (by simp)
      rcases List.mem_append.mp hack with ha' | ha'
      · obtain ⟨X, tX, lgX, h1, h2, h3, h5, h6, h4⟩ := hca v T m lgp ha' k hk
        refine ⟨X, tX, lgX, leaderLog_mono h1, h2, ?_, h5, ?_⟩
        · -- the grant needed an unspent vote, so the witness predates this term
          have hUterm : U = t1 := by
            rw [hev1] at hgact
            rw [Protocol.step] at hgact
            exact (handleRequestVote_grant hgact).2.2.2.2
          have hfree : (w.nodes v).currentTerm < t1 ∨ (w.nodes v).votedFor = none := by
            rw [hev1] at hgact
            rw [Protocol.step] at hgact
            exact handleRequestVote_grant_free hgact
          have hpost : ((w.act v ev).nodes v).currentTerm = U := by
            rw [act_nodes_self, hev1, Protocol.step]
            exact (handleRequestVote_grant (by rw [hev1, Protocol.step] at hgact; exact hgact)).2.1
          have hmono := act_term_mono w v ev v
          rw [act_nodes_self] at hmono hpost
          rcases hfree with hq | hq
          · omega
          · have : tX ≠ (w.nodes v).currentTerm := by
              intro hc; exact (h6 hc) hq
            omega
        · rw [hlgeq, hlogsame]; exact h4
      · -- both fresh is impossible: one step cannot both grant and acknowledge
        exfalso
        have hcur : ((w.act v ev).nodes v).currentTerm = T := fresh_ack_term ha'
        have hUt : ((w.act v ev).nodes v).currentTerm = U := by
          rw [act_nodes_self, hev1, Protocol.step]
          exact (handleRequestVote_grant (by rw [hev1, Protocol.step] at hgact; exact hgact)).2.1
        omega
  cases hs with
  | deliver s d m0 hd hm => exact key d _ rfl
  | electionTimeout k hk => exact key k _ rfl
  | heartbeat k hk => exact key k _ rfl
  | client k rid cmd hk => exact key k _ rfl
  | crash k hk =>
      intro v T m lgp hack U lgv hvote hTU k' hk'
      rw [crash_acks] at hack; rw [crash_voteLogs] at hvote
      obtain ⟨X, tX, lgX, h1, h2, h3, h5, h4⟩ := h v T m lgp hack U lgv hvote hTU k' hk'
      exact ⟨X, tX, lgX, by rw [crash_leaderLogs]; exact h1, h2, h3, h5, h4⟩

/-- **Vote-time attribution holds in every reachable world.** -/
theorem voteAttributed_reachable {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) : VoteAttributed w := by
  induction h with
  | init => exact voteAttributed_init members
  | tail hr hs ih => exact voteAttributed_step hnd hr ih hs

/--
**Attribution at election time.**

As `VoteAttributed`, but about the log a node was elected with — needed for the
case where the intersecting node is the new leader itself, which votes for
itself without sending a grant.
-/
def ElectedAttributed (w : World σ κ) : Prop :=
  ∀ (v T m : Nat) (lgp : σ), (v, T, m, lgp) ∈ w.acks →
    ∀ (U : Nat) (lgel : σ), (v, U, lgel) ∈ w.elected → T < U → ∀ k, k ≤ m →
      ∃ (X tX : Nat) (lgX : σ), (X, tX, lgX) ∈ w.leaderLogs ∧ T ≤ tX ∧ tX < U
        ∧ (T = tX → k ≤ LogStore.lastIndex lgX)
        ∧ LogStore.get lgel k = LogStore.get lgX k

theorem electedAttributed_init (members : List Nat) :
    ElectedAttributed (σ := σ) (κ := κ) (World.init members) := by
  intro v T m lgp h; simp [World.init] at h

theorem electedAttributed_step {members : List Nat} {w w' : World σ κ}
    (hnd : members.Nodup) (hr : Reachable members w)
    (h : ElectedAttributed w) (hs : Step members w w') : ElectedAttributed w' := by
  have hr' : Reachable members w' := Reachable.tail hr hs
  have hca := changeAttributed_reachable hnd hr
  have hle := eInv_reachable hnd hr
  have hlb := ledInv_reachable hnd hr
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev → ElectedAttributed w' := by
    intro j ev hw
    subst hw
    intro v T m lgp hack U lgel hel hTU k hk
    rcases List.mem_append.mp hel with he' | he'
    · rcases List.mem_append.mp hack with ha' | ha'
      · obtain ⟨X, tX, lgX, h1, h2, h3, h4⟩ := h v T m lgp ha' U lgel he' hTU k hk
        exact ⟨X, tX, lgX, leaderLog_mono h1, h2, h3, h4⟩
      · -- a fresh acknowledgement cannot predate an older election of a higher term
        exfalso
        obtain ⟨hvj, _⟩ := mem_ackOf ha'
        subst hvj
        have hUle : U ≤ (w.nodes v).currentTerm :=
          hlb.bound v U (hle.led v U lgel he')
        have hcur : ((w.act v ev).nodes v).currentTerm = T := fresh_ack_term ha'
        have hmono := act_term_mono w v ev v
        omega
    · -- a fresh election record: its log is the node's current log
      obtain ⟨h1, h2, h3, h4, h5⟩ := mem_electedOf he'
      subst h1
      rcases List.mem_append.mp hack with ha' | ha'
      · obtain ⟨X, tX, lgX, hX1, hX2, hX3, hX5, hX6, hX4⟩ := hca v T m lgp ha' k hk
        refine ⟨X, tX, lgX, leaderLog_mono hX1, hX2, ?_, hX5, ?_⟩
        · -- no snapshot of this term can exist before the node assumes leadership
          have hterm := step_term_mono (w.nodes v) ev
          rcases Nat.lt_or_ge tX (Protocol.step (w.nodes v) ev).1.currentTerm with hq | hq
          · rw [h2]; exact hq
          · exfalso
            have htX : tX = (w.nodes v).currentTerm := by omega
            have hXled : (X, tX) ∈ w.led := (llInv_reachable hnd hr).led X tX lgX hX1
            have hvled : (v, tX) ∈ (w.act v ev).led := by
              rw [act_led]
              refine List.mem_append_right _ ?_
              have := ledOf_self (j := v) (s := (Protocol.step (w.nodes v) ev).1) h4
              rw [show (Protocol.step (w.nodes v) ev).1.currentTerm = tX by omega] at this
              exact this
            have hXv : X = v :=
              led_unique hnd hr' (by rw [act_led]; exact List.mem_append_left _ hXled) hvled
            subst hXv
            -- a node that has led `tX` can never campaign in `tX` again, and
            -- assuming leadership without a term change means it just did
            have := led_not_candidate_term_gt hnd hr hXled
              (leader_from_candidate h4 h5 (by omega))
            omega
        · have hq : LogStore.get lgel k = LogStore.get (w.nodes v).log k := by
            rw [h3]
            exact congrArg (fun l => LogStore.get l k) (leader_log_unchanged h4 h5)
          rw [hq]; exact hX4
      · -- both fresh: the node cannot both acknowledge and assume leadership
        exfalso
        have hcur : ((w.act v ev).nodes v).currentTerm = T := fresh_ack_term ha'
        rw [act_nodes_self] at hcur
        exact absurd (h2.trans hcur) (by omega)
  cases hs with
  | deliver s d m hd hm => exact key d _ rfl
  | electionTimeout k hk => exact key k _ rfl
  | heartbeat k hk => exact key k _ rfl
  | client k rid cmd hk => exact key k _ rfl
  | crash k hk =>
      intro v T m lgp hack U lgel hel hTU k' hk'
      rw [crash_acks] at hack; rw [crash_elected] at hel
      obtain ⟨X, tX, lgX, h1, h2, h3, h5, h4⟩ := h v T m lgp hack U lgel hel hTU k' hk'
      exact ⟨X, tX, lgX, by rw [crash_leaderLogs]; exact h1, h2, h3, h5, h4⟩

theorem electedAttributed_reachable {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) : ElectedAttributed w := by
  induction h with
  | init => exact electedAttributed_init members
  | tail hr hs ih => exact electedAttributed_step hnd hr ih hs

/-! ## The log a leader was elected with predates its own term -/

/-- An election record's log carries no entry of the term just won. -/
def ElectedTermLt (w : World σ κ) : Prop :=
  ∀ X U (lgel : σ), (X, U, lgel) ∈ w.elected → LogStore.lastTerm lgel < U

theorem electedTermLt_init (members : List Nat) :
    ElectedTermLt (σ := σ) (κ := κ) (World.init members) := by
  intro X U lgel h; simp [World.init] at h

theorem electedTermLt_step {members : List Nat} {w w' : World σ κ}
    (hnd : members.Nodup) (hr : Reachable members w)
    (h : ElectedTermLt w) (hs : Step members w w') : ElectedTermLt w' := by
  have hr' : Reachable members w' := Reachable.tail hr hs
  have hled := ledInv_reachable hnd hr
  have hcin := cInv_reachable hnd hr
  have hb := (tInv_reachable hr).logs
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev → ElectedTermLt w' := by
    intro j ev hw
    subst hw
    intro X U lgel hmem
    rcases List.mem_append.mp hmem with h' | h'
    · exact h X U lgel h'
    · obtain ⟨h1, h2, h3, h4, h5⟩ := mem_electedOf h'
      subst h1
      have hlogpre : (Protocol.step (w.nodes X) ev).1.log = (w.nodes X).log :=
        leader_log_unchanged h4 h5
      have hgoal : LogStore.lastTerm lgel = LogStore.lastTerm (w.nodes X).log := by
        rw [h3]; exact congrArg LogStore.lastTerm hlogpre
      rw [hgoal, h2]
      -- suppose the log already carried an entry of the term just won
      rcases Nat.lt_or_ge (LogStore.lastTerm (w.nodes X).log)
        (Protocol.step (w.nodes X) ev).1.currentTerm with hlt | hge
      · exact hlt
      exfalso
      have hle : LogStore.lastTerm (w.nodes X).log
          ≤ (Protocol.step (w.nodes X) ev).1.currentTerm := by
        rcases Nat.eq_zero_or_pos (LogStore.lastIndex (w.nodes X).log) with h0 | h0
        · unfold LogStore.lastTerm LogStore.termAt
          rw [h0]; simp
        · obtain ⟨x, hx⟩ : ∃ x, LogStore.get (w.nodes X).log
              (LogStore.lastIndex (w.nodes X).log) = some x := by
            cases hq : LogStore.get (w.nodes X).log (LogStore.lastIndex (w.nodes X).log) with
            | none =>
                exfalso
                have := (LogStore.get_isSome_iff (w.nodes X).log
                  (LogStore.lastIndex (w.nodes X).log)).mpr ⟨by omega, Nat.le_refl _⟩
                rw [hq] at this; exact Bool.noConfusion this
            | some x => exact ⟨x, rfl⟩
          have hlt : LogStore.lastTerm (w.nodes X).log = x.term := by
            unfold LogStore.lastTerm LogStore.termAt; rw [hx]; rfl
          have := hb X _ x hx
          have hmono := step_term_mono (w.nodes X) ev
          omega
      have heq : LogStore.lastTerm (w.nodes X).log
          = (Protocol.step (w.nodes X) ev).1.currentTerm := by omega
      have hidx : 1 ≤ LogStore.lastIndex (w.nodes X).log := by
        rcases Nat.eq_zero_or_pos (LogStore.lastIndex (w.nodes X).log) with h0 | h0
        · exfalso
          have hz : LogStore.lastTerm (w.nodes X).log = 0 := by
            unfold LogStore.lastTerm LogStore.termAt
            rw [h0]; simp
          have hp := roleTermPos_reachable hr' X (by
            rw [act_nodes_self]
            intro hq; exact Role.noConfusion (h4 ▸ hq))
          rw [act_nodes_self] at hp
          omega
        · exact h0
      obtain ⟨x, hx⟩ : ∃ x, LogStore.get (w.nodes X).log
          (LogStore.lastIndex (w.nodes X).log) = some x := by
        cases hq : LogStore.get (w.nodes X).log (LogStore.lastIndex (w.nodes X).log) with
        | none =>
            exfalso
            have := (LogStore.get_isSome_iff (w.nodes X).log
              (LogStore.lastIndex (w.nodes X).log)).mpr ⟨by omega, Nat.le_refl _⟩
            rw [hq] at this; exact Bool.noConfusion this
        | some x => exact ⟨x, rfl⟩
      have hxt : x.term = (Protocol.step (w.nodes X) ev).1.currentTerm := by
        unfold LogStore.lastTerm LogStore.termAt at heq; rw [hx] at heq; simpa using heq
      obtain ⟨c, hc⟩ := (bInv_reachable hr).logs X _ x hx
      have hledc : (c, x.term) ∈ w.led := hcin.ledRec c _ x hc
      -- both `c` and `X` won this term, so they are the same node
      have hwonc : WonTerm members (w.act X ev) c x.term :=
        wonTerm_act ((ledInv_reachable hnd hr).won c x.term hledc) _ _
      have hwonX : WonTerm members (w.act X ev) X x.term := by
        have ha := allInv_reachable hr'
        have hlead' : ((w.act X ev).nodes X).role = Role.leader := by
          rw [act_nodes_self]; exact h4
        have := wonTerm_of_leader ha.leader.votes ha.leader.quorum ha.ghost hlead'
        rw [act_nodes_self, ← hxt] at this
        exact this
      have hcX : c = X := everWinner_unique hnd hr' hwonc hwonX
      subst hcX
      have hbnd := hled.bound c x.term hledc
      have hmono := step_term_mono (w.nodes c) ev
      have hterm : (w.nodes c).currentTerm = x.term := by omega
      exact hled.leads c x.term hledc hterm
        (leader_from_candidate h4 h5 (by omega))
  cases hs with
  | deliver s d m hd hm => exact key d _ rfl
  | electionTimeout k hk => exact key k _ rfl
  | heartbeat k hk => exact key k _ rfl
  | client k rid cmd hk => exact key k _ rfl
  | crash k hk =>
      intro X U lgel hm; rw [crash_elected] at hm; exact h X U lgel hm

theorem electedTermLt_reachable {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) : ElectedTermLt w := by
  induction h with
  | init => exact electedTermLt_init members
  | tail hr hs ih => exact electedTermLt_step hnd hr ih hs

end RaftKV.Proof
