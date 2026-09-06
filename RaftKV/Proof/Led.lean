import RaftKV.Proof.LeaderStable
import RaftKV.Proof.FullLog

/-!
# Leadership as a durable record

`World.led` is proof-only ghost state recording every `(node, term)` pair for
which the node has ever held leadership.

Its purpose is to turn `leader_stable` — a statement about a single step — into
a statement about all of history: **a node recorded as having led term `t` is
still the leader whenever its term is still `t`.** Contrapositively, once such a
node is a follower or candidate, its term has already moved past `t`.

That is what rules out the awkward scenario the log-level proofs must exclude: a
node leading term `t`, losing leadership, and re-acquiring it in the same term
with a different log.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [KVStore κ]

theorem act_led (w : World σ κ) (j : Nat) (ev : Event) :
    (w.act j ev).led = w.led ++ ledOf j (Protocol.step (w.nodes j) ev).1 := rfl

theorem mem_ledOf {i j t : Nat} {s : NodeState σ κ} (h : (i, t) ∈ ledOf j s) :
    i = j ∧ t = s.currentTerm ∧ s.role = Role.leader := by
  unfold ledOf at h
  split at h
  · rename_i hr
    simp only [List.mem_singleton, Prod.mk.injEq] at h
    exact ⟨h.1, h.2, hr⟩
  · simp at h

theorem ledOf_self {j : Nat} {s : NodeState σ κ} (h : s.role = Role.leader) :
    (j, s.currentTerm) ∈ ledOf j s := by
  unfold ledOf; rw [if_pos h]; simp

/-- A recorded leadership term never exceeds the node's current term. -/
def LedBound (w : World σ κ) : Prop := ∀ i t, (i, t) ∈ w.led → t ≤ (w.nodes i).currentTerm

/--
**A node that has led term `t` never campaigns in `t` again.**

The natural claim would be that it *still leads* while its term is `t`, and that
was the invariant before crashes were modelled. A crash falsifies it: the node
comes back a follower in the same term. What survives — and what the argument
actually needs — is that it can never re-enter *candidacy* in that term, because
the only road to candidacy is `startElection`, which advances the term.
-/
def LedNotCandidate (w : World σ κ) : Prop :=
  ∀ i t, (i, t) ∈ w.led → (w.nodes i).currentTerm = t → (w.nodes i).role ≠ Role.candidate

/-- Every recorded leadership is backed by a won election. -/
def LedWon (members : List Nat) (w : World σ κ) : Prop :=
  ∀ i t, (i, t) ∈ w.led → WonTerm members w i t

/-- A node that currently leads is on record as leading its term. -/
def LeaderLed (w : World σ κ) : Prop :=
  ∀ i, (w.nodes i).role = Role.leader → (i, (w.nodes i).currentTerm) ∈ w.led

/-- The leadership-record invariants. -/
structure LedInv (members : List Nat) (w : World σ κ) : Prop where
  /-- Recorded terms are in the past. -/
  bound : LedBound w
  /-- A recorded leader never campaigns again in that term. -/
  leads : LedNotCandidate w
  /-- Recorded leaders won their term. -/
  won : LedWon members w
  /-- Current leaders are on record. -/
  cur : LeaderLed w

theorem ledInv_init (members : List Nat) :
    LedInv (σ := σ) (κ := κ) members (World.init members) where
  bound := by intro i t h; simp [World.init] at h
  leads := by intro i t h; simp [World.init] at h
  won := by intro i t h; simp [World.init] at h
  cur := by
    intro i h
    exact absurd h (by simp [World.init, Protocol.initState])

/-- **The leadership records are preserved by every step.** -/
theorem ledInv_step {members : List Nat} {w w' : World σ κ}
    (hnd : members.Nodup) (hr : Reachable members w)
    (h : LedInv members w) (hs : Step members w w') : LedInv members w' := by
  have hterm : ∀ i, (w.nodes i).currentTerm ≤ (w'.nodes i).currentTerm := world_term_mono hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i t hmem
    cases hs with
    | deliver s d m hd hm =>
        rcases List.mem_append.mp (act_led w d _ ▸ hmem) with h' | h'
        · exact Nat.le_trans (h.bound i t h') (hterm i)
        · obtain ⟨h1, h2, _⟩ := mem_ledOf h'
          subst h1; rw [act_nodes_self]; exact Nat.le_of_eq h2
    | electionTimeout k hk =>
        rcases List.mem_append.mp (act_led w k _ ▸ hmem) with h' | h'
        · exact Nat.le_trans (h.bound i t h') (hterm i)
        · obtain ⟨h1, h2, _⟩ := mem_ledOf h'
          subst h1; rw [act_nodes_self]; exact Nat.le_of_eq h2
    | heartbeat k hk =>
        rcases List.mem_append.mp (act_led w k _ ▸ hmem) with h' | h'
        · exact Nat.le_trans (h.bound i t h') (hterm i)
        · obtain ⟨h1, h2, _⟩ := mem_ledOf h'
          subst h1; rw [act_nodes_self]; exact Nat.le_of_eq h2
    | client k rid cmd hk =>
        rcases List.mem_append.mp (act_led w k _ ▸ hmem) with h' | h'
        · exact Nat.le_trans (h.bound i t h') (hterm i)
        · obtain ⟨h1, h2, _⟩ := mem_ledOf h'
          subst h1; rw [act_nodes_self]; exact Nat.le_of_eq h2
    | crash k hk =>
        exact Nat.le_trans (h.bound i t (by rwa [crash_led] at hmem)) (hterm i)
  · intro i t hmem heq
    -- A fresh record belongs to a leader; an old one cannot have become a
    -- candidate, since campaigning advances the term.
    have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev →
        (w'.nodes i).role ≠ Role.candidate := by
      intro j ev hw
      subst hw
      rcases List.mem_append.mp (act_led w j ev ▸ hmem) with h' | h'
      · have hb := h.bound i t h'
        have hle : (w.nodes i).currentTerm ≤ ((w.act j ev).nodes i).currentTerm :=
          act_term_mono w j ev i
        have hold : (w.nodes i).currentTerm = t := by omega
        have hnc : (w.nodes i).role ≠ Role.candidate := h.leads i t h' hold
        by_cases hij : i = j
        · subst hij
          rw [act_nodes_self]
          intro hcand
          rcases step_candidate_term (w.nodes i) ev hcand with hq | hq
          · exact hnc hq
          · rw [act_nodes_self] at heq; omega
        · rw [act_nodes_ne _ _ _ hij]; exact hnc
      · obtain ⟨h1, _, h3⟩ := mem_ledOf h'
        subst h1; rw [act_nodes_self, h3]; exact fun hq => Role.noConfusion hq
    cases hs with
    | deliver s d m hd hm => exact key d _ rfl
    | electionTimeout k hk => exact key k _ rfl
    | heartbeat k hk => exact key k _ rfl
    | client k rid cmd hk => exact key k _ rfl
    | crash k hk =>
        -- a restart comes back a follower
        by_cases hij : i = k
        · subst hij; rw [crash_nodes_self, restart_role]; exact fun hq => Role.noConfusion hq
        · rw [crash_nodes_ne _ _ hij]
          rw [crash_nodes_ne _ _ hij] at heq
          exact h.leads i t (by rwa [crash_led] at hmem) heq
  · intro i t hmem
    have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev → WonTerm members w' i t := by
      intro j ev hw
      subst hw
      rcases List.mem_append.mp (act_led w j ev ▸ hmem) with h' | h'
      · exact wonTerm_act (h.won i t h') _ _
      · obtain ⟨h1, h2, h3⟩ := mem_ledOf h'
        have ha := allInv_reachable (Reachable.tail hr hs)
        have hlead : ((w.act j ev).nodes j).role = Role.leader := by
          rw [act_nodes_self]; exact h3
        have hw := wonTerm_of_leader ha.leader.votes ha.leader.quorum ha.ghost hlead
        rw [act_nodes_self] at hw
        rw [h1, h2]; exact hw
    cases hs with
    | deliver s d m hd hm => exact key d _ rfl
    | electionTimeout k hk => exact key k _ rfl
    | heartbeat k hk => exact key k _ rfl
    | client k rid cmd hk => exact key k _ rfl
    | crash k hk =>
        obtain ⟨V, h1, h2, h3, h4⟩ := h.won i t (by rwa [crash_led] at hmem)
        exact ⟨V, h1, h2, h3, fun v hv => by rw [crash_votes]; exact h4 v hv⟩
  · intro i hlead
    have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev →
        (i, (w'.nodes i).currentTerm) ∈ w'.led := by
      intro j ev hw
      subst hw
      rw [act_led]
      by_cases hij : i = j
      · subst hij
        rw [act_nodes_self] at hlead ⊢
        exact List.mem_append_right _ (ledOf_self hlead)
      · rw [act_nodes_ne _ _ _ hij] at hlead ⊢
        exact List.mem_append_left _ (h.cur i hlead)
    cases hs with
    | deliver s d m hd hm => exact key d _ rfl
    | electionTimeout k hk => exact key k _ rfl
    | heartbeat k hk => exact key k _ rfl
    | client k rid cmd hk => exact key k _ rfl
    | crash k hk =>
        rw [crash_led]
        by_cases hij : i = k
        · subst hij; rw [crash_nodes_self, restart_role] at hlead; exact absurd hlead (by simp)
        · rw [crash_nodes_ne _ _ hij] at hlead ⊢; exact h.cur i hlead

/-- The leadership records hold in every reachable world. -/
theorem ledInv_reachable {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) : LedInv members w := by
  induction h with
  | init => exact ledInv_init members
  | tail hr hs ih => exact ledInv_step hnd hr ih hs

/--
**Leadership of a term is unique across all of history.**

If two nodes are both recorded as having led term `t`, they are the same node.
-/
theorem led_unique {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) {i j t : Nat}
    (hi : (i, t) ∈ w.led) (hj : (j, t) ∈ w.led) : i = j := by
  have hl := ledInv_reachable hnd hrch
  exact everWinner_unique hnd hrch (hl.won i t hi) (hl.won j t hj)

/--
A node recorded as having led term `t` that is *not* currently a leader has
necessarily moved on to a strictly later term.
-/
theorem led_not_candidate_term_gt {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) {i t : Nat}
    (hmem : (i, t) ∈ w.led) (hnl : (w.nodes i).role = Role.candidate) :
    t < (w.nodes i).currentTerm := by
  have hl := ledInv_reachable hnd hrch
  have hb := hl.bound i t hmem
  rcases Nat.lt_or_ge t (w.nodes i).currentTerm with h | h
  · exact h
  · exact absurd hnl (hl.leads i t hmem (Nat.le_antisymm h hb))


/--
**A node that has led term `t` keeps its log for as long as its term is `t`.**

This is the crash-proof replacement for "a recorded leader still leads". A log
shrinks only by accepting an `appendEntries`, and a same-term payload could only
have come from the term's winner — which is this node — while no packet is ever
self-addressed. So nothing can truncate it, whether or not it is still in office.
-/
theorem led_log_stable {members : List Nat} {w w' : World σ κ} [LawfulLogStore σ]
    (hnd : members.Nodup) (hr : Reachable members w) (hs : Step members w w') {i t : Nat}
    (hled : (i, t) ∈ w.led) (hold : (w.nodes i).currentTerm = t)
    (hnew : (w'.nodes i).currentTerm = t) :
    (w'.nodes i).log = (w.nodes i).log
      ∨ ∃ e, (w'.nodes i).log = LogStore.append (w.nodes i).log e := by
  have hp := pInv_reachable hr
  have hwon : WonTerm members w i t := (ledInv_reachable hnd hr).won i t hled
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev →
      (∀ src m', ev = Event.recv src m' → (src, j, m') ∈ w.sent) →
      (w'.nodes i).log = (w.nodes i).log
        ∨ ∃ e, (w'.nodes i).log = LogStore.append (w.nodes i).log e := by
    intro j ev hw hdel
    subst hw
    by_cases hij : i = j
    · subst hij
      rw [act_nodes_self]
      rcases step_log (w.nodes i) ev with hl | ⟨rid, cmd, _, hl⟩ |
        ⟨src, term, l, pi, pt, es, lc, hev, hl, _, _, _, hct⟩
      · exact Or.inl hl
      · exact Or.inr ⟨_, hl⟩
      · exfalso
        subst hev
        have hterm : term = t := by
          rw [act_nodes_self, Protocol.step, handleAppendEntries_term_eq] at hnew
          omega
        subst hterm
        have hpkt := hdel src (Msg.appendEntries term l pi pt es lc) rfl
        have hwin : WonTerm members w src term := hp.aeWinner src i term l pi pt es lc hpkt
        have hsi : src = i := everWinner_unique hnd hr hwin (hold ▸ hwon)
        subst hsi
        exact hp.notSelf (src, src, Msg.appendEntries term l pi pt es lc) hpkt (by simp)
    · rw [act_nodes_ne _ _ _ hij]; exact Or.inl rfl
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
      by_cases hij : i = k
      · subst hij; rw [crash_nodes_self, restart_log]; exact Or.inl rfl
      · rw [crash_nodes_ne _ _ hij]; exact Or.inl rfl

/--
The same for the **logical** log: a leader still holding its term has either not
touched it or appended to it.

The proof is `led_log_stable`'s, one branch at a time, over `fullStep` instead
of `step` — which is the point of defining the logical log to take the same
operations.
-/
theorem led_full_stable {members : List Nat} {w w' : World σ κ} [LawfulLogStore σ]
    (hnd : members.Nodup) (hr : Reachable members w) (hs : Step members w w') {i t : Nat}
    (hled : (i, t) ∈ w.led) (hold : (w.nodes i).currentTerm = t)
    (hnew : (w'.nodes i).currentTerm = t) :
    w'.full i = w.full i ∨ ∃ e, w'.full i = LogStore.append (w.full i) e := by
  have hp := pInv_reachable hr
  have hwon : WonTerm members w i t := (ledInv_reachable hnd hr).won i t hled
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev →
      (∀ src m', ev = Event.recv src m' → (src, j, m') ∈ w.sent) →
      w'.full i = w.full i ∨ ∃ e, w'.full i = LogStore.append (w.full i) e := by
    intro j ev hw hdel
    subst hw
    by_cases hij : i = j
    · subst hij
      rw [act_full_self]
      rcases full_step (w.nodes i) (w.full i) ev with hl | ⟨rid, cmd, _, _, hl⟩ |
        ⟨src, term, l, pi, pt, es, lc, hev, ha, hl⟩
      · exact Or.inl hl
      · exact Or.inr ⟨_, hl⟩
      · exfalso
        subst hev
        have hct := aeAccepts_term ha
        have hterm : term = t := by
          rw [act_nodes_self, Protocol.step, handleAppendEntries_term_eq] at hnew
          omega
        subst hterm
        have hpkt := hdel src (Msg.appendEntries term l pi pt es lc) rfl
        have hwin : WonTerm members w src term := hp.aeWinner src i term l pi pt es lc hpkt
        have hsi : src = i := everWinner_unique hnd hr hwin (hold ▸ hwon)
        subst hsi
        exact hp.notSelf (src, src, Msg.appendEntries term l pi pt es lc) hpkt (by simp)
    · rw [act_full_ne _ _ _ hij]; exact Or.inl rfl
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
  | crash k hk => exact Or.inl rfl

end RaftKV.Proof
