import RaftKV.Proof.Chain

/-!
# The log a leader was elected with

Leader Completeness is a claim about the log a leader held **at the moment it
won its term** — a fact no current-state predicate can express once that leader
has advanced. `World.elected` captures it as ghost state.

Two facts are established here:

* `electedPrefix` — while a leader still holds the term it was elected for, the
  log it was elected with is a prefix of its current log. Leaders only ever
  append (`leader_log_monotone`) and cannot be demoted within their term
  (`leader_stable`), so nothing it was elected with can have been rewritten.
* `elected_unique` — a term has at most one election record, since it has at
  most one winner (`led_unique`).
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [LawfulLogStore σ] [KVStore κ]

theorem act_elected (w : World σ κ) (j : Nat) (ev : Event) :
    (w.act j ev).elected
      = w.elected ++ electedOf j (w.nodes j) (Protocol.step (w.nodes j) ev).1 (fullStep (w.nodes j) (w.full j) ev) := rfl

theorem mem_electedOf {i j t : Nat} {lg : σ} {pre post : NodeState σ κ} {fl : σ}
    (h : (i, t, lg) ∈ electedOf j pre post fl) :
    i = j ∧ t = post.currentTerm ∧ lg = fl
      ∧ post.role = Role.leader ∧ pre.role ≠ Role.leader := by
  unfold electedOf at h
  split at h
  · rename_i hc
    simp only [List.mem_singleton, Prod.mk.injEq] at h
    exact ⟨h.1, h.2.1, h.2.2, hc.1, hc.2⟩
  · simp at h

theorem elected_mono {w : World σ κ} {j : Nat} {ev : Event} {i t : Nat} {lg : σ}
    (h : (i, t, lg) ∈ w.elected) : (i, t, lg) ∈ (w.act j ev).elected := by
  rw [act_elected]; exact List.mem_append_left _ h

/-- Election records are backed by the leadership ledger. -/
def ElectedLed (w : World σ κ) : Prop :=
  ∀ i t lg, (i, t, lg) ∈ w.elected → (i, t) ∈ w.led

/-- While a leader still holds its term, the log it was elected with is a prefix. -/
def ElectedPrefix (w : World σ κ) : Prop :=
  ∀ i t lg, (i, t, lg) ∈ w.elected → (w.nodes i).currentTerm = t →
    ∀ k, k ≤ LogStore.lastIndex lg →
      LogStore.get (w.full i) k = LogStore.get lg k

/-- And the current log reaches at least as far as the record. -/
def ElectedReach (w : World σ κ) : Prop :=
  ∀ i t lg, (i, t, lg) ∈ w.elected → (w.nodes i).currentTerm = t →
    LogStore.lastIndex lg ≤ LogStore.lastIndex (w.full i)

/-- The election-record invariants. -/
structure EInv (members : List Nat) (w : World σ κ) : Prop where
  /-- Records are in the ledger. -/
  led : ElectedLed w
  /-- Records are prefixes of the current log. -/
  prefixed : ElectedPrefix w
  /-- The current log reaches at least as far. -/
  reaches : ElectedReach w

theorem eInv_init (members : List Nat) :
    EInv (σ := σ) (κ := κ) members (World.init members) where
  led := by intro i t lg h; simp [World.init] at h
  prefixed := by intro i t lg h; simp [World.init] at h
  reaches := by intro i t lg h; simp [World.init] at h

/-- **The election-record invariants are preserved by every step.** -/
theorem eInv_step {members : List Nat} {w w' : World σ κ}
    (hnd : members.Nodup) (hr : Reachable members w)
    (h : EInv members w) (hs : Step members w w') : EInv members w' := by
  have hl := ledInv_reachable hnd hr
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev → EInv members w' := by
    intro j ev hw
    subst hw
    constructor
    · intro i t lg hmem
      rw [act_elected] at hmem
      rw [act_led]
      rcases List.mem_append.mp hmem with h' | h'
      · exact List.mem_append_left _ (h.led i t lg h')
      · obtain ⟨h1, h2, h3, h4, _⟩ := mem_electedOf h'
        subst h1
        refine List.mem_append_right _ ?_
        rw [h2]
        exact ledOf_self h4
    · intro i t lg hmem hterm k hk
      rw [act_elected] at hmem
      rcases List.mem_append.mp hmem with h' | h'
      · by_cases hij : i = j
        · subst hij
          rw [act_nodes_self] at hterm
          -- the leader still holds its term, so it is still in office and only appended
          have hled : (i, t) ∈ w.led := h.led i t lg h'
          have hb := hl.bound i t hled
          have hmono := act_term_mono w i ev i
          rw [act_nodes_self] at hmono
          have hold : (w.nodes i).currentTerm = t := by omega
          have hpre := h.prefixed i t lg h' hold
          rcases led_full_stable hnd hr hs hled hold (by rw [act_nodes_self]; exact hterm)
            with hlog | ⟨e', hlog⟩
          · rw [act_full_self] at hlog; rw [act_full_self, hlog]; exact hpre k hk
          · rw [act_full_self] at hlog
            rw [act_full_self, hlog, LogStore.get_append, if_neg ?_]
            · exact hpre k hk
            · -- `k` is within the old log, so it is not the freshly appended slot
              rcases Nat.eq_zero_or_pos k with hk0 | hk0
              · omega
              · have hreach := h.reaches i t lg h' hold
                omega
        · rw [act_nodes_ne _ _ _ hij] at hterm
          rw [act_full_ne _ _ _ hij]
          exact h.prefixed i t lg h' hterm k hk
      · obtain ⟨h1, h2, h3, h4, _⟩ := mem_electedOf h'
        subst h1; subst h3
        rw [act_full_self]
    · -- the logical log reaches at least as far as the record
      intro i t lg hmem hterm
      rw [act_elected] at hmem
      rcases List.mem_append.mp hmem with h' | h'
      · by_cases hij : i = j
        · subst hij
          rw [act_nodes_self] at hterm
          have hled : (i, t) ∈ w.led := h.led i t lg h'
          have hb := hl.bound i t hled
          have hmono := act_term_mono w i ev i
          rw [act_nodes_self] at hmono
          have hold : (w.nodes i).currentTerm = t := by omega
          have hreach := h.reaches i t lg h' hold
          rcases led_full_stable hnd hr hs hled hold (by rw [act_nodes_self]; exact hterm)
            with hlog | ⟨e', hlog⟩
          · rw [act_full_self] at hlog; rw [act_full_self, hlog]; exact hreach
          · rw [act_full_self] at hlog
            rw [act_full_self, hlog, LogStore.lastIndex_append]; omega
        · rw [act_nodes_ne _ _ _ hij] at hterm
          rw [act_full_ne _ _ _ hij]
          exact h.reaches i t lg h' hterm
      · obtain ⟨h1, h2, h3, h4, _⟩ := mem_electedOf h'
        subst h1; subst h3
        rw [act_full_self]
        exact Nat.le_refl _
  cases hs with
  | deliver s d m hd hm => exact key d _ rfl
  | electionTimeout k hk => exact key k _ rfl
  | heartbeat k hk => exact key k _ rfl
  | client k rid cmd hk => exact key k _ rfl
  | crash k hk =>
      -- the election record is a ghost and the log it names is durable
      refine ⟨?_, ?_, ?_⟩
      · intro i t lg hm; rw [crash_elected] at hm; rw [crash_led]; exact h.led i t lg hm
      · intro i t lg hm hterm k' hk'
        rw [crash_elected] at hm
        rw [crash_full]
        by_cases hij : i = k
        · subst hij
          rw [crash_nodes_self, restart_currentTerm] at hterm
          exact h.prefixed i t lg hm hterm k' hk'
        · rw [crash_nodes_ne _ _ hij] at hterm; exact h.prefixed i t lg hm hterm k' hk'
      · intro i t lg hm hterm
        rw [crash_elected] at hm
        rw [crash_full]
        by_cases hij : i = k
        · subst hij
          rw [crash_nodes_self, restart_currentTerm] at hterm
          exact h.reaches i t lg hm hterm
        · rw [crash_nodes_ne _ _ hij] at hterm; exact h.reaches i t lg hm hterm

/-- The election-record invariants hold in every reachable world. -/
theorem eInv_reachable {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) : EInv members w := by
  induction h with
  | init => exact eInv_init members
  | tail hr hs ih => exact eInv_step hnd hr ih hs

/-- **A term has at most one election record.** -/
theorem elected_unique {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) {i j t : Nat} {lg₁ lg₂ : σ}
    (h₁ : (i, t, lg₁) ∈ w.elected) (h₂ : (j, t, lg₂) ∈ w.elected) : i = j := by
  have he := eInv_reachable hnd hrch
  exact led_unique hnd hrch (he.led i t lg₁ h₁) (he.led j t lg₂ h₂)

end RaftKV.Proof
