import RaftKV.Proof.Commit

/-!
# Entry terms never exceed their holder's term

A replica cannot hold an entry stamped with a term it has not yet reached, and a
replication payload cannot carry entries from beyond the term it is sent in.

This is the first half of "log terms are non-decreasing", which the remaining
Leader Completeness argument needs in order to compare a candidate's `lastTerm`
against a voter's.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [LawfulLogStore σ] [KVStore κ]

/-- No replica holds an entry from a term it has not reached. -/
def LogTermsBounded (w : World σ κ) : Prop :=
  ∀ (i k : Nat) (e : Entry),
    LogStore.get (w.nodes i).log k = some e → e.term ≤ (w.nodes i).currentTerm

/-- No payload carries entries from beyond its own term. -/
def MsgTermsBounded (w : World σ κ) : Prop :=
  ∀ (src dst t l pi pt : Nat) (es : List Entry) (lc n : Nat) (e : Entry),
    (src, dst, Msg.appendEntries t l pi pt es lc) ∈ w.sent → es[n]? = some e → e.term ≤ t

/-- The term-bound invariants. -/
structure TInv (members : List Nat) (w : World σ κ) : Prop where
  /-- Logs are bounded. -/
  logs : LogTermsBounded w
  /-- Payloads are bounded. -/
  msgs : MsgTermsBounded w

theorem tInv_init (members : List Nat) : TInv (σ := σ) (κ := κ) members (World.init members) where
  logs := by
    intro i k e h
    exfalso
    rw [World.init] at h
    simp only [Protocol.initState] at h
    have hs := (LogStore.get_isSome_iff (LogStore.empty : σ) k).mp (by rw [h]; rfl)
    simp only [LogStore.lastIndex_empty] at hs
    omega
  msgs := by intro src dst t l pi pt es lc n e h; simp [World.init] at h

/-- **The term-bound invariants are preserved by every step.** -/
theorem tInv_step {members : List Nat} {w w' : World σ κ}
    (h : TInv members w) (hs : Step members w w') : TInv members w' := by
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev →
      (∀ src m', ev = Event.recv src m' → (src, j, m') ∈ w.sent) →
      TInv members w' := by
    intro j ev hw hdel
    subst hw
    have hlogs : LogTermsBounded (w.act j ev) := by
      intro i k e hget
      by_cases hij : i = j
      · subst hij
        rw [act_nodes_self] at hget ⊢
        have hmono := step_term_mono (w.nodes i) ev
        rcases step_log (w.nodes i) ev with hl | ⟨rid, cmd, hev, hl⟩ |
          ⟨src, term, l, pi, pt, es, lc, hev, hl, hpi, _, _, _⟩
        · rw [hl] at hget
          exact Nat.le_trans (h.logs i k e hget) hmono
        · rw [hl, LogStore.get_append] at hget
          by_cases hk : k = LogStore.lastIndex (w.nodes i).log + 1
          · rw [if_pos hk] at hget
            have he : e = { term := (w.nodes i).currentTerm, cmd := cmd, reqId := rid } :=
              (Option.some.inj hget).symm
            rw [he]
            exact hmono
          · rw [if_neg hk] at hget
            exact Nat.le_trans (h.logs i k e hget) hmono
        · subst hev
          rw [hl] at hget
          refine appendFrom_mem
            (fun _ e' => e'.term ≤ (Protocol.step (w.nodes i)
              (Event.recv src (Msg.appendEntries term l pi pt es lc))).1.currentTerm)
            es (w.nodes i).log (pi + 1) (by omega) (by omega) ?_ ?_ k e hget
          · intro k' e' hk'
            exact Nat.le_trans (h.logs i k' e' hk') hmono
          · intro n e' hn
            have hb := h.msgs src i term l pi pt es lc n e'
              (hdel src (Msg.appendEntries term l pi pt es lc) rfl) hn
            have : term ≤ (Protocol.step (w.nodes i)
                (Event.recv src (Msg.appendEntries term l pi pt es lc))).1.currentTerm := by
              rw [Protocol.step, handleAppendEntries_term_eq]; omega
            omega
      · rw [act_nodes_ne _ _ _ hij] at hget ⊢
        exact h.logs i k e hget
    refine ⟨hlogs, ?_⟩
    intro src dst t l pi pt es lc n e hp hn
    rw [act_sent] at hp
    rcases List.mem_append.mp hp with hp' | hp'
    · exact h.msgs src dst t l pi pt es lc n e hp' hn
    · rcases mem_sendsOf hp' with ⟨to, m, heq, hact⟩
      have hsj : src = j := congrArg (fun q => q.1) heq
      have hm : m = Msg.appendEntries t l pi pt es lc := by
        have := congrArg (fun q => q.2.2) heq; simpa using this.symm
      subst hm; subst hsj
      obtain ⟨p0, hp0⟩ := step_appendEntries_payload hact
      simp only [appendEntriesTo] at hp0
      obtain ⟨htt, _, hpi, _, hes, _⟩ := Msg.appendEntries.inj hp0
      have hni : max 1 (PeerMap.get (Protocol.step (w.nodes src) ev).1.nextIndex p0
          (LogStore.lastIndex (Protocol.step (w.nodes src) ev).1.log + 1)) = pi + 1 := by
        rw [hpi]
        have := Nat.le_max_left 1
          (PeerMap.get (Protocol.step (w.nodes src) ev).1.nextIndex p0
            (LogStore.lastIndex (Protocol.step (w.nodes src) ev).1.log + 1))
        omega
      rw [hes] at hn
      have hget := appendEntriesTo_entries (s := (Protocol.step (w.nodes src) ev).1) (p := p0) hn
      rw [hni] at hget
      have := hlogs src (pi + 1 + n) e (by rw [act_nodes_self]; exact hget)
      rw [act_nodes_self] at this
      omega
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

/-- **Entry terms never exceed their holder's term, in any reachable world.** -/
theorem tInv_reachable {members : List Nat} {w : World σ κ} (h : Reachable members w) :
    TInv members w := by
  induction h with
  | init => exact tInv_init members
  | tail _ hs ih => exact tInv_step ih hs

/-! ## Terms are positive -/

/-- A node that is campaigning or leading has advanced past term zero. -/
def RoleTermPos (w : World σ κ) : Prop :=
  ∀ i, (w.nodes i).role ≠ Role.follower → 1 ≤ (w.nodes i).currentTerm

theorem roleTermPos_init (members : List Nat) :
    RoleTermPos (σ := σ) (κ := κ) (World.init members) := by
  intro i h; exact absurd rfl h

theorem roleTermPos_step {members : List Nat} {w w' : World σ κ}
    (h : RoleTermPos w) (hs : Step members w w') : RoleTermPos w' := by
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev → RoleTermPos w' := by
    intro j ev hw
    subst hw
    intro i hne
    by_cases hij : i = j
    · subst hij
      rw [act_nodes_self] at hne ⊢
      rcases step_votes_char hne with ⟨hev, _, _⟩ | ⟨hold, hterm, _⟩
      · subst hev
        rw [Protocol.step] at hne ⊢
        by_cases hlead : (w.nodes i).role == Role.leader
        · rw [if_pos hlead] at hne ⊢
          exact h i hne
        · rw [if_neg hlead] at hne ⊢
          rw [startElection_term]; omega
      · rw [hterm]; exact h i hold
    · rw [act_nodes_ne _ _ _ hij] at hne ⊢; exact h i hne
  cases hs with
  | deliver s d m hd hm => exact key d _ rfl
  | electionTimeout k hk => exact key k _ rfl
  | heartbeat k hk => exact key k _ rfl
  | client k rid cmd hk => exact key k _ rfl

theorem roleTermPos_reachable {members : List Nat} {w : World σ κ} (h : Reachable members w) :
    RoleTermPos w := by
  induction h with
  | init => exact roleTermPos_init members
  | tail _ hs ih => exact roleTermPos_step ih hs

/-- Every minted entry carries a positive term. -/
def CreatedTermPos (w : World σ κ) : Prop :=
  ∀ (c k : Nat) (e : Entry), (c, k, e) ∈ w.created → 1 ≤ e.term

theorem createdTermPos_init (members : List Nat) :
    CreatedTermPos (σ := σ) (κ := κ) (World.init members) := by
  intro c k e h; simp [World.init] at h

theorem createdTermPos_step {members : List Nat} {w w' : World σ κ}
    (hr : Reachable members w) (h : CreatedTermPos w) (hs : Step members w w') :
    CreatedTermPos w' := by
  have hpos := roleTermPos_reachable (Reachable.tail hr hs)
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev → CreatedTermPos w' := by
    intro j ev hw
    subst hw
    intro c k e hmem
    rw [act_created] at hmem
    rcases List.mem_append.mp hmem with h' | h'
    · exact h c k e h'
    · obtain ⟨h1, hlead, hterm, _, _⟩ := createdOf_get h'
      subst h1
      have := hpos c (by rw [act_nodes_self, hlead]; exact fun hq => Role.noConfusion hq)
      rw [act_nodes_self] at this
      omega
  cases hs with
  | deliver s d m hd hm => exact key d _ rfl
  | electionTimeout k hk => exact key k _ rfl
  | heartbeat k hk => exact key k _ rfl
  | client k rid cmd hk => exact key k _ rfl

/-- **Every entry ever minted carries a positive term.** -/
theorem createdTermPos_reachable {members : List Nat} {w : World σ κ}
    (h : Reachable members w) : CreatedTermPos w := by
  induction h with
  | init => exact createdTermPos_init members
  | tail hr hs ih => exact createdTermPos_step hr ih hs

/-- Entries in any well-formed log carry positive terms. -/
theorem wf_term_pos {members : List Nat} {w : World σ κ}
    (hrch : Reachable members w) {lg : σ} (hwf : WellFormedLog w lg)
    {k : Nat} {e : Entry} (g : LogStore.get lg k = some e) : 1 ≤ e.term := by
  obtain ⟨c, hc⟩ := hwf.created k e g
  exact createdTermPos_reachable hrch c k e hc

/-! ## Log terms are non-decreasing -/

/-- A recorded predecessor term never exceeds the term of the entry above it. -/
def ChainSorted (w : World σ κ) : Prop :=
  ∀ (idx : Nat) (e : Entry) (p : Nat), (idx, e, p) ∈ w.chain → p ≤ e.term

theorem chainSorted_init (members : List Nat) :
    ChainSorted (σ := σ) (κ := κ) (World.init members) := by
  intro idx e p h; simp [World.init] at h

theorem chainSorted_step {members : List Nat} {w w' : World σ κ}
    (hr : Reachable members w) (h : ChainSorted w) (hs : Step members w w') : ChainSorted w' := by
  have ht' := (tInv_reachable (Reachable.tail hr hs)).logs
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev → ChainSorted w' := by
    intro j ev hw
    subst hw
    intro idx e p hmem
    rw [act_chain] at hmem
    rcases List.mem_append.mp hmem with h' | h'
    · exact h idx e p h'
    · obtain ⟨hlead, hidx, hterm, rid, cmd, hev⟩ := mem_chainOf h'
      -- the recorded predecessor is an entry of the same leader, whose terms are bounded
      cases hq : LogStore.get (Protocol.step (w.nodes j) ev).1.log (idx - 1) with
      | none =>
          have : p = 0 := by
            unfold chainOf at h'
            subst hev
            dsimp only at h'
            rw [if_pos hlead] at h'
            simp only [List.mem_singleton, Prod.mk.injEq] at h'
            rw [h'.2.2, ← h'.1, LogStore.termAt, hq]; rfl
          omega
      | some v =>
          have hpv : p = v.term := by
            unfold chainOf at h'
            subst hev
            dsimp only at h'
            rw [if_pos hlead] at h'
            simp only [List.mem_singleton, Prod.mk.injEq] at h'
            rw [h'.2.2, ← h'.1, LogStore.termAt, hq]; rfl
          have hvb := ht' j (idx - 1) v (by rw [act_nodes_self]; exact hq)
          rw [act_nodes_self] at hvb
          omega
  cases hs with
  | deliver s d m hd hm => exact key d _ rfl
  | electionTimeout k hk => exact key k _ rfl
  | heartbeat k hk => exact key k _ rfl
  | client k rid cmd hk => exact key k _ rfl

theorem chainSorted_reachable {members : List Nat} {w : World σ κ} (h : Reachable members w) :
    ChainSorted w := by
  induction h with
  | init => exact chainSorted_init members
  | tail hr hs ih => exact chainSorted_step hr ih hs

/--
**Log terms are non-decreasing.**

In any well-formed log, an entry at a lower index never has a higher term. This
is what lets a comparison of two logs' *last* terms say something about their
contents at shared indices, which is exactly what the `upToDate` check needs to
be useful.
-/
theorem wf_terms_sorted {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) {lg : σ} (hwf : WellFormedLog w lg) :
    ∀ (d k₁ k₂ : Nat) (e₁ e₂ : Entry), k₂ - k₁ ≤ d →
      LogStore.get lg k₁ = some e₁ → LogStore.get lg k₂ = some e₂ → k₁ ≤ k₂ →
      e₁.term ≤ e₂.term := by
  intro d
  induction d with
  | zero =>
      intro k₁ k₂ e₁ e₂ hd g₁ g₂ hk
      have hkk : k₁ = k₂ := by omega
      subst hkk
      rw [g₁] at g₂
      have hee : e₁ = e₂ := Option.some.inj g₂
      subst hee
      exact Nat.le_refl _
  | succ n ih =>
      intro k₁ k₂ e₁ e₂ hd g₁ g₂ hk
      by_cases heq : k₁ = k₂
      · subst heq
        rw [g₁] at g₂
        have hee : e₁ = e₂ := Option.some.inj g₂
        subst hee
        exact Nat.le_refl _
      · have hk1 : 1 ≤ k₁ := ((LogStore.get_isSome_iff lg k₁).mp (by rw [g₁]; rfl)).1
        have hk2 : 2 ≤ k₂ := by omega
        obtain ⟨p, hp1, hp2⟩ := hwf.chained k₂ e₂ g₂ hk2
        have hple : p ≤ e₂.term := chainSorted_reachable hrch k₂ e₂ p hp1
        obtain ⟨v, hv⟩ : ∃ v, LogStore.get lg (k₂ - 1) = some v := by
          unfold LogStore.termAt at hp2
          cases hq : LogStore.get lg (k₂ - 1) with
          | none => rw [hq] at hp2; simp at hp2
          | some v => exact ⟨v, rfl⟩
        have hvt : v.term = p := by
          unfold LogStore.termAt at hp2
          rw [hv] at hp2; simpa using hp2
        have := ih k₁ (k₂ - 1) e₁ v (by omega) g₁ hv (by omega)
        omega

/-- Convenient form of `wf_terms_sorted` without the explicit fuel. -/
theorem wf_sorted {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) {lg : σ} (hwf : WellFormedLog w lg)
    {k₁ k₂ : Nat} {e₁ e₂ : Entry}
    (g₁ : LogStore.get lg k₁ = some e₁) (g₂ : LogStore.get lg k₂ = some e₂) (hk : k₁ ≤ k₂) :
    e₁.term ≤ e₂.term :=
  wf_terms_sorted hnd hrch hwf k₂ k₁ k₂ e₁ e₂ (by omega) g₁ g₂ hk

/--
**A log's last term bounds every term in it.**

Immediate from sortedness, and the form the `upToDate` comparison actually uses.
-/
theorem wf_le_lastTerm {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) {lg : σ} (hwf : WellFormedLog w lg)
    {k : Nat} {e : Entry} (g : LogStore.get lg k = some e) :
    e.term ≤ LogStore.lastTerm lg := by
  have hk := (LogStore.get_isSome_iff lg k).mp (by rw [g]; rfl)
  obtain ⟨v, hv⟩ : ∃ v, LogStore.get lg (LogStore.lastIndex lg) = some v := by
    cases hq : LogStore.get lg (LogStore.lastIndex lg) with
    | none =>
        exfalso
        have := (LogStore.get_isSome_iff lg (LogStore.lastIndex lg)).mpr ⟨by omega, Nat.le_refl _⟩
        rw [hq] at this; exact Bool.noConfusion this
    | some v => exact ⟨v, rfl⟩
  have hlt : LogStore.lastTerm lg = v.term := by
    unfold LogStore.lastTerm LogStore.termAt
    rw [hv]; rfl
  rw [hlt]
  exact wf_sorted hnd hrch hwf g hv hk.2

end RaftKV.Proof
