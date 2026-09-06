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
      = w.elected ++ electedOf j (w.nodes j) (Protocol.step (w.nodes j) ev).1 := rfl

theorem mem_electedOf {i j t : Nat} {lg : σ} {pre post : NodeState σ κ}
    (h : (i, t, lg) ∈ electedOf j pre post) :
    i = j ∧ t = post.currentTerm ∧ lg = post.log
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
      LogStore.get (w.nodes i).log k = LogStore.get lg k

/-- The election-record invariants. -/
structure EInv (members : List Nat) (w : World σ κ) : Prop where
  /-- Records are in the ledger. -/
  led : ElectedLed w
  /-- Records are prefixes of the current log. -/
  prefixed : ElectedPrefix w

theorem eInv_init (members : List Nat) :
    EInv (σ := σ) (κ := κ) members (World.init members) where
  led := by intro i t lg h; simp [World.init] at h
  prefixed := by intro i t lg h; simp [World.init] at h

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
          rw [act_nodes_self] at hterm ⊢
          -- the leader still holds its term, so it is still in office and only appended
          have hled : (i, t) ∈ w.led := h.led i t lg h'
          have hb := hl.bound i t hled
          have hmono := act_term_mono w i ev i
          rw [act_nodes_self] at hmono
          have hold : (w.nodes i).currentTerm = t := by omega
          have hpre := h.prefixed i t lg h' hold
          have hlead : (w.nodes i).role = Role.leader := hl.leads i t hled hold
          have hlead' : ((w.act i ev).nodes i).role = Role.leader := by
            rcases leader_stable hnd hr hs hlead with ⟨h1, _⟩ | h2
            · exact h1
            · exfalso; rw [hold] at h2; rw [act_nodes_self] at h2; omega
          rcases leader_log_monotone hs hlead hlead' with hlog | ⟨e', hlog⟩
          · rw [act_nodes_self] at hlog; rw [hlog]; exact hpre k hk
          · rw [act_nodes_self] at hlog
            rw [hlog, LogStore.get_append, if_neg ?_]
            · exact hpre k hk
            · -- `k` is within the old log, so it is not the freshly appended slot
              rcases Nat.eq_zero_or_pos k with hk0 | hk0
              · omega
              · have hsome : (LogStore.get lg k).isSome :=
                  (LogStore.get_isSome_iff lg k).mpr ⟨hk0, hk⟩
                have : (LogStore.get (w.nodes i).log k).isSome := by
                  rw [hpre k hk]; exact hsome
                have := ((LogStore.get_isSome_iff (w.nodes i).log k).mp this).2
                omega
        · rw [act_nodes_ne _ _ _ hij] at hterm ⊢
          exact h.prefixed i t lg h' hterm k hk
      · obtain ⟨h1, h2, h3, h4, _⟩ := mem_electedOf h'
        subst h1; subst h3
        rw [act_nodes_self]
  cases hs with
  | deliver s d m hd hm => exact key d _ rfl
  | electionTimeout k hk => exact key k _ rfl
  | heartbeat k hk => exact key k _ rfl
  | client k rid cmd hk => exact key k _ rfl

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
