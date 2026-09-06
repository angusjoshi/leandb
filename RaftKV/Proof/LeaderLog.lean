import RaftKV.Proof.TermBound
import RaftKV.Proof.VoteDom

/-!
# The term-`t` leader's log, as a durable object

Leader Completeness has to speak of *the* term-`t` leader's log long after that
leader has died. `World.leaderLogs` snapshots a leader's log at every step at
which it leads, and the facts below make those snapshots behave like a single
growing object:

* `LeaderLogPrefix` — while a leader still holds its term, every snapshot it has
  taken is a prefix of its current log;
* `LeaderLogsChain` — consequently any two snapshots for the same `(node, term)`
  are prefix-comparable;
* `CreatedInLeaderLog` — every entry a leader mints appears in one of its own
  snapshots.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [LawfulLogStore σ] [KVStore κ]

/-- `lg₁` is a prefix of `lg₂`: they agree everywhere `lg₁` has entries. -/
def PrefixOf (lg₁ lg₂ : σ) : Prop :=
  ∀ k, k ≤ LogStore.lastIndex lg₁ → LogStore.get lg₂ k = LogStore.get lg₁ k

theorem PrefixOf.refl (lg : σ) : PrefixOf lg lg := fun _ _ => rfl

/-- A prefix is no longer than what it is a prefix of. -/
theorem PrefixOf.len {a b : σ} [LawfulLogStore σ] (h : PrefixOf a b) :
    LogStore.lastIndex a ≤ LogStore.lastIndex b := by
  rcases Nat.eq_zero_or_pos (LogStore.lastIndex a) with h0 | h0
  · omega
  · have hs : (LogStore.get a (LogStore.lastIndex a)).isSome :=
      (LogStore.get_isSome_iff a (LogStore.lastIndex a)).mpr ⟨by omega, Nat.le_refl _⟩
    have : (LogStore.get b (LogStore.lastIndex a)).isSome := by
      rw [h (LogStore.lastIndex a) (Nat.le_refl _)]; exact hs
    exact ((LogStore.get_isSome_iff b (LogStore.lastIndex a)).mp this).2

theorem PrefixOf.trans {a b c : σ} (h₁ : PrefixOf a b) (h₂ : PrefixOf b c)
    (hlen : LogStore.lastIndex a ≤ LogStore.lastIndex b) : PrefixOf a c := by
  intro k hk
  rw [h₂ k (by omega), h₁ k hk]

/-- Appending extends a prefix. -/
theorem PrefixOf.append {a b : σ} (h : PrefixOf a b) (e : Entry) :
    PrefixOf a (LogStore.append b e) := by
  intro k hk
  rw [LogStore.get_append, if_neg, h k hk]
  -- `k` lies inside `a`, hence inside `b`, so it is not the fresh slot
  intro hcon
  have hs : (LogStore.get a k).isSome := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso; omega
    · exact (LogStore.get_isSome_iff a k).mpr ⟨h0, hk⟩
  have : (LogStore.get b k).isSome := by rw [h k hk]; exact hs
  have := ((LogStore.get_isSome_iff b k).mp this).2
  omega

theorem act_leaderLogs (w : World σ κ) (j : Nat) (ev : Event) :
    (w.act j ev).leaderLogs
      = w.leaderLogs ++ leaderLogOf j (Protocol.step (w.nodes j) ev).1 := rfl

theorem mem_leaderLogOf {i j t : Nat} {lg : σ} {s : NodeState σ κ}
    (h : (i, t, lg) ∈ leaderLogOf j s) :
    i = j ∧ t = s.currentTerm ∧ lg = s.log ∧ s.role = Role.leader := by
  unfold leaderLogOf at h
  split at h
  · rename_i hr
    simp only [List.mem_singleton, Prod.mk.injEq] at h
    exact ⟨h.1, h.2.1, h.2.2, hr⟩
  · simp at h

theorem leaderLog_mono {w : World σ κ} {j : Nat} {ev : Event} {i t : Nat} {lg : σ}
    (h : (i, t, lg) ∈ w.leaderLogs) : (i, t, lg) ∈ (w.act j ev).leaderLogs := by
  rw [act_leaderLogs]; exact List.mem_append_left _ h

theorem leaderLogOf_self {j : Nat} {s : NodeState σ κ} (h : s.role = Role.leader) :
    (j, s.currentTerm, s.log) ∈ leaderLogOf j s := by
  unfold leaderLogOf; rw [if_pos h]; simp

/-- A snapshot's owner is on record as leading that term. -/
def LeaderLogLed (w : World σ κ) : Prop :=
  ∀ i t (lg : σ), (i, t, lg) ∈ w.leaderLogs → (i, t) ∈ w.led

/-- Snapshots are prefixes of the current log while the term stands. -/
def LeaderLogPrefix (w : World σ κ) : Prop :=
  ∀ i t (lg : σ), (i, t, lg) ∈ w.leaderLogs → (w.nodes i).currentTerm = t →
    PrefixOf lg (w.nodes i).log

/-- Snapshots for one `(node, term)` are totally ordered by prefix. -/
def LeaderLogsChain (w : World σ κ) : Prop :=
  ∀ i t (lg₁ lg₂ : σ), (i, t, lg₁) ∈ w.leaderLogs → (i, t, lg₂) ∈ w.leaderLogs →
    PrefixOf lg₁ lg₂ ∨ PrefixOf lg₂ lg₁

/-- Every minted entry appears in one of its creator's snapshots. -/
def CreatedInLeaderLog (w : World σ κ) : Prop :=
  ∀ c k (e : Entry), (c, k, e) ∈ w.created →
    ∃ lg : σ, (c, e.term, lg) ∈ w.leaderLogs ∧ LogStore.get lg k = some e

/-- The leader-log invariants. -/
structure LLInv (members : List Nat) (w : World σ κ) : Prop where
  /-- Snapshot owners are on record. -/
  led : LeaderLogLed w
  /-- Snapshots are prefixes of the current log. -/
  pre : LeaderLogPrefix w
  /-- Snapshots for a term form a chain. -/
  chain : LeaderLogsChain w
  /-- Creations are recorded in a snapshot. -/
  created : CreatedInLeaderLog w

theorem llInv_init (members : List Nat) :
    LLInv (σ := σ) (κ := κ) members (World.init members) where
  led := by intro i t lg h; simp [World.init] at h
  pre := by intro i t lg h; simp [World.init] at h
  chain := by intro i t lg₁ lg₂ h; simp [World.init] at h
  created := by intro c k e h; simp [World.init] at h

/-- **The leader-log invariants are preserved by every step.** -/
theorem llInv_step {members : List Nat} {w w' : World σ κ}
    (hnd : members.Nodup) (hr : Reachable members w)
    (h : LLInv members w) (hs : Step members w w') : LLInv members w' := by
  have hl := ledInv_reachable hnd hr
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev → LLInv members w' := by
    intro j ev hw
    subst hw
    have hled : LeaderLogLed (w.act j ev) := by
      intro i t lg hmem
      rw [act_leaderLogs] at hmem
      rw [act_led]
      rcases List.mem_append.mp hmem with h' | h'
      · exact List.mem_append_left _ (h.led i t lg h')
      · obtain ⟨h1, h2, _, h4⟩ := mem_leaderLogOf h'
        subst h1
        refine List.mem_append_right _ ?_
        rw [h2]
        exact ledOf_self h4
    have hpre : LeaderLogPrefix (w.act j ev) := by
      intro i t lg hmem hterm
      rw [act_leaderLogs] at hmem
      rcases List.mem_append.mp hmem with h' | h'
      · by_cases hij : i = j
        · subst hij
          rw [act_nodes_self] at hterm ⊢
          -- the term did not move, so the node is still leading and only appended
          have hledr : (i, t) ∈ w.led := h.led i t lg h'
          have hb := hl.bound i t hledr
          have hmono := act_term_mono w i ev i
          rw [act_nodes_self] at hmono
          have hold : (w.nodes i).currentTerm = t := by omega
          have hpo := h.pre i t lg h' hold
          rcases led_log_stable hnd hr hs hledr hold (by rw [act_nodes_self]; exact hterm)
            with hlog | ⟨e', hlog⟩
          · rw [act_nodes_self] at hlog; rw [hlog]; exact hpo
          · rw [act_nodes_self] at hlog; rw [hlog]; exact hpo.append e'
        · rw [act_nodes_ne _ _ _ hij] at hterm ⊢
          exact h.pre i t lg h' hterm
      · obtain ⟨h1, _, h3, _⟩ := mem_leaderLogOf h'
        subst h1; subst h3
        rw [act_nodes_self]
        exact PrefixOf.refl _
    refine ⟨hled, hpre, ?_, ?_⟩
    · -- chain: a fresh snapshot extends every old one for the same node and term
      intro i t lg₁ lg₂ hm₁ hm₂
      rw [act_leaderLogs] at hm₁ hm₂
      have fresh : ∀ (lgo lgn : σ), (i, t, lgo) ∈ w.leaderLogs →
          (i, t, lgn) ∈ leaderLogOf j (Protocol.step (w.nodes j) ev).1 → PrefixOf lgo lgn := by
        intro lgo lgn ho hn
        obtain ⟨h1, h2, h3, _⟩ := mem_leaderLogOf hn
        subst h1; subst h3
        have := hpre i t lgo (by rw [act_leaderLogs]; exact List.mem_append_left _ ho)
          (by rw [act_nodes_self]; exact h2.symm)
        rwa [act_nodes_self] at this
      rcases List.mem_append.mp hm₁ with h₁ | h₁ <;>
        rcases List.mem_append.mp hm₂ with h₂ | h₂
      · exact h.chain i t lg₁ lg₂ h₁ h₂
      · exact Or.inl (fresh lg₁ lg₂ h₁ h₂)
      · exact Or.inr (fresh lg₂ lg₁ h₂ h₁)
      · obtain ⟨_, _, hq₁, _⟩ := mem_leaderLogOf h₁
        obtain ⟨_, _, hq₂, _⟩ := mem_leaderLogOf h₂
        subst hq₁; subst hq₂
        exact Or.inl (PrefixOf.refl _)
    · -- creations: the minting step also snapshots the leader's log
      intro c k e hmem
      rw [act_created] at hmem
      rcases List.mem_append.mp hmem with h' | h'
      · obtain ⟨lg, hlg1, hlg2⟩ := h.created c k e h'
        exact ⟨lg, leaderLog_mono hlg1, hlg2⟩
      · obtain ⟨h1, hlead, hterm, _, hget⟩ := createdOf_get h'
        subst h1
        refine ⟨(Protocol.step (w.nodes c) ev).1.log, ?_, hget⟩
        rw [act_leaderLogs]
        refine List.mem_append_right _ ?_
        rw [hterm]
        exact leaderLogOf_self hlead
  cases hs with
  | deliver s d m hd hm => exact key d _ rfl
  | electionTimeout k hk => exact key k _ rfl
  | heartbeat k hk => exact key k _ rfl
  | client k rid cmd hk => exact key k _ rfl
  | crash k hk =>
      -- snapshots and the ledger are ghosts; the log a snapshot prefixes is durable
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i t lg hm; rw [crash_leaderLogs] at hm; rw [crash_led]; exact h.led i t lg hm
      · intro i t lg hm hterm
        rw [crash_leaderLogs] at hm
        by_cases hik : i = k
        · subst hik
          rw [crash_nodes_self, restart_log]
          rw [crash_nodes_self, restart_currentTerm] at hterm
          exact h.pre i t lg hm hterm
        · rw [crash_nodes_ne _ _ hik] at hterm ⊢; exact h.pre i t lg hm hterm
      · intro i t lg₁ lg₂ h₁ h₂
        rw [crash_leaderLogs] at h₁ h₂; exact h.chain i t lg₁ lg₂ h₁ h₂
      · intro c k' e hm
        rw [crash_created] at hm
        obtain ⟨lg, h1, h2⟩ := h.created c k' e hm
        exact ⟨lg, by rw [crash_leaderLogs]; exact h1, h2⟩

/-- A node that currently leads has its current log on record. -/
def LeaderNowRecorded (w : World σ κ) : Prop :=
  ∀ i, (w.nodes i).role = Role.leader →
    (i, (w.nodes i).currentTerm, (w.nodes i).log) ∈ w.leaderLogs

theorem leaderNowRecorded_init (members : List Nat) :
    LeaderNowRecorded (σ := σ) (κ := κ) (World.init members) := by
  intro i h; exact absurd h (by simp [World.init, Protocol.initState])

theorem leaderNowRecorded_step {members : List Nat} {w w' : World σ κ}
    (h : LeaderNowRecorded w) (hs : Step members w w') : LeaderNowRecorded w' := by
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev → LeaderNowRecorded w' := by
    intro j ev hw
    subst hw
    intro i hlead
    rw [act_leaderLogs]
    by_cases hij : i = j
    · subst hij
      rw [act_nodes_self] at hlead ⊢
      exact List.mem_append_right _ (leaderLogOf_self hlead)
    · rw [act_nodes_ne _ _ _ hij] at hlead ⊢
      exact List.mem_append_left _ (h i hlead)
  cases hs with
  | deliver s d m hd hm => exact key d _ rfl
  | electionTimeout k hk => exact key k _ rfl
  | heartbeat k hk => exact key k _ rfl
  | client k rid cmd hk => exact key k _ rfl
  | crash k hk =>
      intro i hlead
      rw [crash_leaderLogs]
      by_cases hik : i = k
      · subst hik; rw [crash_nodes_self, restart_role] at hlead; exact absurd hlead (by simp)
      · rw [crash_nodes_ne _ _ hik] at hlead ⊢; exact h i hlead

theorem leaderNowRecorded_reachable {members : List Nat} {w : World σ κ}
    (h : Reachable members w) : LeaderNowRecorded w := by
  induction h with
  | init => exact leaderNowRecorded_init members
  | tail _ hs ih => exact leaderNowRecorded_step ih hs

/-- Leader-log snapshots are well-formed logs. -/
def LeaderLogWF (w : World σ κ) : Prop :=
  ∀ i t (lg : σ), (i, t, lg) ∈ w.leaderLogs → WellFormedLog w lg

theorem leaderLogWF_init (members : List Nat) :
    LeaderLogWF (σ := σ) (κ := κ) (World.init members) := by
  intro i t lg h; simp [World.init] at h

theorem leaderLogWF_step {members : List Nat} {w w' : World σ κ}
    (hnd : members.Nodup) (hr : Reachable members w)
    (h : LeaderLogWF w) (hs : Step members w w') : LeaderLogWF w' := by
  have hr' : Reachable members w' := Reachable.tail hr hs
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev → LeaderLogWF w' := by
    intro j ev hw
    subst hw
    intro i t lg hmem
    rw [act_leaderLogs] at hmem
    rcases List.mem_append.mp hmem with h' | h'
    · exact (h i t lg h').mono
    · obtain ⟨_, _, h3, _⟩ := mem_leaderLogOf h'
      have hq : ((w.act j ev).nodes j).log = lg := by rw [act_nodes_self]; exact h3.symm
      rw [← hq]; exact wf_node hnd hr' j
  cases hs with
  | deliver s d m hd hm => exact key d _ rfl
  | electionTimeout k hk => exact key k _ rfl
  | heartbeat k hk => exact key k _ rfl
  | client k rid cmd hk => exact key k _ rfl
  | crash k hk =>
      intro i t lg hm; rw [crash_leaderLogs] at hm; exact (h i t lg hm).crashMono

theorem leaderLogWF_reachable {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) : LeaderLogWF w := by
  induction h with
  | init => exact leaderLogWF_init members
  | tail hr hs ih => exact leaderLogWF_step hnd hr ih hs

/-- Every leader-log snapshot has an election record behind it. -/
def LeaderLogHasElected (w : World σ κ) : Prop :=
  ∀ X U (lgX : σ), (X, U, lgX) ∈ w.leaderLogs →
    ∃ lgel : σ, (X, U, lgel) ∈ w.elected ∧ PrefixOf lgel lgX

theorem leaderLogHasElected_init (members : List Nat) :
    LeaderLogHasElected (σ := σ) (κ := κ) (World.init members) := by
  intro X U lgX h; simp [World.init] at h

theorem leaderLogHasElected_step {members : List Nat} {w w' : World σ κ}
    (hnd : members.Nodup) (hr : Reachable members w)
    (h : LeaderLogHasElected w) (hs : Step members w w') : LeaderLogHasElected w' := by
  have hnow := leaderNowRecorded_reachable hr
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev → LeaderLogHasElected w' := by
    intro j ev hw
    subst hw
    intro X U lgX hmem
    rw [act_leaderLogs] at hmem
    rcases List.mem_append.mp hmem with h' | h'
    · obtain ⟨lgel, h1, h2⟩ := h X U lgX h'
      exact ⟨lgel, elected_mono h1, h2⟩
    · obtain ⟨h1, h2, h3, h4⟩ := mem_leaderLogOf h'
      subst h1; subst h3
      by_cases hpl : (w.nodes X).role = Role.leader
      · -- already leading: reuse the election behind the earlier snapshot
        have hterm : (w.nodes X).currentTerm = U := by
          rw [h2]
          rcases step_votes_char (by rw [h4]; exact fun hq => Role.noConfusion hq) with
            ⟨hev, _, _⟩ | ⟨_, ht, _⟩
          · subst hev
            rw [Protocol.step, if_pos (by rw [hpl]; simp)]
          · exact ht.symm
        obtain ⟨lgel, he1, he2⟩ := h X U (w.nodes X).log (hterm ▸ hnow X hpl)
        refine ⟨lgel, elected_mono he1, ?_⟩
        refine PrefixOf.trans he2 ?_ he2.len
        -- the leader only ever appended
        rcases leader_log_monotone hs hpl (by rw [act_nodes_self]; exact h4) with hl | ⟨e, hl⟩
        · rw [act_nodes_self] at hl; rw [hl]; exact PrefixOf.refl _
        · rw [act_nodes_self] at hl; rw [hl]; exact (PrefixOf.refl _).append e
      · -- just elected: the election record is this very snapshot
        refine ⟨(Protocol.step (w.nodes X) ev).1.log, ?_, PrefixOf.refl _⟩
        rw [act_elected, h2]
        refine List.mem_append_right _ ?_
        unfold electedOf
        rw [if_pos ⟨h4, hpl⟩]
        simp
  cases hs with
  | deliver s d m hd hm => exact key d _ rfl
  | electionTimeout k hk => exact key k _ rfl
  | heartbeat k hk => exact key k _ rfl
  | client k rid cmd hk => exact key k _ rfl
  | crash k hk =>
      intro X U lgX hm
      rw [crash_leaderLogs] at hm
      obtain ⟨lgel, h1, h2⟩ := h X U lgX hm
      exact ⟨lgel, by rw [crash_elected]; exact h1, h2⟩

theorem leaderLogHasElected_reachable {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) : LeaderLogHasElected w := by
  induction h with
  | init => exact leaderLogHasElected_init members
  | tail hr hs ih => exact leaderLogHasElected_step hnd hr ih hs

/-- The leader-log invariants hold in every reachable world. -/
theorem llInv_reachable {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) : LLInv members w := by
  induction h with
  | init => exact llInv_init members
  | tail hr hs ih => exact llInv_step hnd hr ih hs

/--
**The term-`t` leader's log contains everything committed at term `t`.**

Two snapshots of the same leader's log in the same term are prefix-comparable,
so whichever is longer contains both.
-/
theorem leaderLog_both {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) {i t : Nat} {lg₁ lg₂ : σ}
    (h₁ : (i, t, lg₁) ∈ w.leaderLogs) (h₂ : (i, t, lg₂) ∈ w.leaderLogs)
    {k₁ k₂ : Nat} {e₁ e₂ : Entry}
    (g₁ : LogStore.get lg₁ k₁ = some e₁) (g₂ : LogStore.get lg₂ k₂ = some e₂) :
    ∃ lg : σ, (i, t, lg) ∈ w.leaderLogs
      ∧ LogStore.get lg k₁ = some e₁ ∧ LogStore.get lg k₂ = some e₂ := by
  rcases (llInv_reachable hnd hrch).chain i t lg₁ lg₂ h₁ h₂ with hp | hp
  · exact ⟨lg₂, h₂, by
      rw [hp k₁ ((LogStore.get_isSome_iff lg₁ k₁).mp (by rw [g₁]; rfl)).2]; exact g₁, g₂⟩
  · exact ⟨lg₁, h₁, g₁, by
      rw [hp k₂ ((LogStore.get_isSome_iff lg₂ k₂).mp (by rw [g₂]; rfl)).2]; exact g₂⟩

end RaftKV.Proof
