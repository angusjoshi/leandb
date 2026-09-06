import RaftKV.Proof.LeaderStable

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

/-- **A node recorded as having led term `t` still leads whenever its term is `t`.** -/
def LedLeader (w : World σ κ) : Prop :=
  ∀ i t, (i, t) ∈ w.led → (w.nodes i).currentTerm = t → (w.nodes i).role = Role.leader

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
  /-- Recorded leaders still lead at their term. -/
  leads : LedLeader w
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
  · intro i t hmem heq
    -- Either the record is fresh (and the node is a leader by construction),
    -- or it is old, in which case `leader_stable` carries leadership across.
    have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev →
        (w'.nodes i).role = Role.leader := by
      intro j ev hw
      subst hw
      rcases List.mem_append.mp (act_led w j ev ▸ hmem) with h' | h'
      · -- old record: its term must already have been `t`
        have hb := h.bound i t h'
        have hle : (w.nodes i).currentTerm ≤ ((w.act j ev).nodes i).currentTerm :=
          act_term_mono w j ev i
        have hold : (w.nodes i).currentTerm = t := by omega
        have hlead : (w.nodes i).role = Role.leader := h.leads i t h' hold
        rcases leader_stable hnd hr hs hlead with ⟨h1, h2⟩ | h2
        · exact h1
        · exfalso; rw [hold] at h2; omega
      · obtain ⟨h1, _, h3⟩ := mem_ledOf h'
        subst h1; rw [act_nodes_self]; exact h3
    cases hs with
    | deliver s d m hd hm => exact key d _ rfl
    | electionTimeout k hk => exact key k _ rfl
    | heartbeat k hk => exact key k _ rfl
    | client k rid cmd hk => exact key k _ rfl
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
theorem led_not_leader_term_gt {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) {i t : Nat}
    (hmem : (i, t) ∈ w.led) (hnl : (w.nodes i).role ≠ Role.leader) :
    t < (w.nodes i).currentTerm := by
  have hl := ledInv_reachable hnd hrch
  have hb := hl.bound i t hmem
  rcases Nat.lt_or_ge t (w.nodes i).currentTerm with h | h
  · exact h
  · exact absurd (hl.leads i t hmem (Nat.le_antisymm h hb)) hnl

end RaftKV.Proof
