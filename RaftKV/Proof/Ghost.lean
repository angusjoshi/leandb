import RaftKV.Proof.Election

/-!
# The ghost vote history

`VoteUnique` in `RaftKV.Proof.Election` is about grants *on the wire*. That is
enough for Election Safety, but not for anything about logs, for two reasons:

* a node's **self-vote** is held in `votedFor` and never transmitted, so `sent`
  cannot witness it; and
* a current-state invariant says nothing once the term-`t` leader has died,
  which is exactly when log-level reasoning still needs to know who won term `t`.

The ghost list `World.votes` records every vote, self-votes included, and only
ever grows. The invariants below mirror those of `Election.lean` over it, and
yield the durable anchor: **at most one node ever wins a term.**
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [KVStore κ]

theorem act_votes (w : World σ κ) (j : Nat) (ev : Event) :
    (w.act j ev).votes = w.votes ++ voteOf j (Protocol.step (w.nodes j) ev).1 := rfl

theorem mem_voteOf {i v c t : Nat} {s : NodeState σ κ} (h : (v, c, t) ∈ voteOf i s) :
    v = i ∧ s.votedFor = some c ∧ t = s.currentTerm := by
  unfold voteOf at h
  cases hv : s.votedFor with
  | none => rw [hv] at h; simp at h
  | some c' =>
      rw [hv] at h
      simp only [List.mem_singleton, Prod.mk.injEq] at h
      exact ⟨h.1, congrArg some h.2.1.symm, h.2.2⟩

theorem voteOf_self {i : Nat} {s : NodeState σ κ} {c : Nat} (h : s.votedFor = some c) :
    (i, c, s.currentTerm) ∈ voteOf i s := by
  unfold voteOf; rw [h]; simp

/-- Ghost votes are backed by the voter's recorded state, exactly as `VoteInv`. -/
def GVoteInv (w : World σ κ) : Prop :=
  ∀ v c t, (v, c, t) ∈ w.votes →
    t ≤ (w.nodes v).currentTerm
      ∧ ((w.nodes v).currentTerm = t → (w.nodes v).votedFor = some c)

/-- **One vote per node per term, self-votes included, for all time.** -/
def GVoteUnique (w : World σ κ) : Prop :=
  ∀ v c₁ c₂ t, (v, c₁, t) ∈ w.votes → (v, c₂, t) ∈ w.votes → c₁ = c₂

/-- Every grant on the wire is also recorded in the ghost history. -/
def GrantRecorded (w : World σ κ) : Prop :=
  ∀ v c t, (v, c, Msg.requestVoteResp t true) ∈ w.sent → (v, c, t) ∈ w.votes

/-- A node's currently held vote — including a self-vote — is in the history. -/
def SelfVoteRecorded (w : World σ κ) : Prop :=
  ∀ i c, (w.nodes i).votedFor = some c → (i, c, (w.nodes i).currentTerm) ∈ w.votes

/-- The ghost invariants, maintained together. -/
structure GInv (members : List Nat) (w : World σ κ) : Prop where
  /-- Ghost votes match voter state. -/
  vote : GVoteInv w
  /-- At most one ghost vote per voter per term. -/
  unique : GVoteUnique w
  /-- Wire grants are recorded. -/
  recorded : GrantRecorded w
  /-- Currently held votes, self-votes included, are recorded. -/
  selfRec : SelfVoteRecorded w

theorem gInv_init (members : List Nat) : GInv (σ := σ) (κ := κ) members (World.init members) where
  vote := by intro v c t h; simp [World.init] at h
  unique := by intro v c₁ c₂ t h; simp [World.init] at h
  recorded := by intro v c t h; simp [World.init] at h
  selfRec := by intro i c h; simp [World.init, Protocol.initState] at h

/--
**The ghost invariants are preserved by every step.**

The argument is the one from `Election.vote_act`, but simpler: the ghost record
names the candidate directly, so no well-formedness side-condition on
`requestVote` messages is needed to interpret it.
-/
theorem gInv_step {members : List Nat} {w w' : World σ κ}
    (hb : Inv members w) (h : GInv members w) (hs : Step members w w') : GInv members w' := by
  have main : ∀ (j : Nat) (ev : Event),
      (∀ src term candId li lt, ev = Event.recv src (Msg.requestVote term candId li lt) →
        candId = src) →
      GInv members (w.act j ev) := by
    intro j ev hev
    have hnew : ∀ v c t, (v, c, t) ∈ voteOf j (Protocol.step (w.nodes j) ev).1 →
        v = j ∧ ((w.act j ev).nodes j).votedFor = some c
          ∧ t = ((w.act j ev).nodes j).currentTerm := by
      intro v c t hp
      obtain ⟨h1, h2, h3⟩ := mem_voteOf hp
      exact ⟨h1, by rw [act_nodes_self]; exact h2, by rw [act_nodes_self]; exact h3⟩
    -- Old ghost records survive because terms only rise and votes are stable.
    have hold : ∀ v c t, (v, c, t) ∈ w.votes →
        t ≤ ((w.act j ev).nodes v).currentTerm
          ∧ (((w.act j ev).nodes v).currentTerm = t →
              ((w.act j ev).nodes v).votedFor = some c) := by
      intro v c t hp
      obtain ⟨hle, himp⟩ := h.vote v c t hp
      by_cases hvj : v = j
      · subst hvj
        rw [act_nodes_self]
        refine ⟨Nat.le_trans hle (step_term_mono _ _), ?_⟩
        intro heq
        have h0 : (w.nodes v).currentTerm = t :=
          Nat.le_antisymm (heq ▸ step_term_mono (w.nodes v) ev) hle
        exact votedFor_stable _ _ _ (by rw [heq, h0]) (himp h0)
      · rw [act_nodes_ne _ _ _ hvj]; exact ⟨hle, himp⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v c t hp
      rw [act_votes] at hp
      rcases List.mem_append.mp hp with hp' | hp'
      · exact hold v c t hp'
      · obtain ⟨hvj, hvf, ht⟩ := hnew v c t hp'
        subst hvj
        exact ⟨Nat.le_of_eq ht, fun _ => hvf⟩
    · intro v c₁ c₂ t hp₁ hp₂
      rw [act_votes] at hp₁ hp₂
      have key : ∀ c c', (v, c, t) ∈ w.votes →
          (v, c', t) ∈ voteOf j (Protocol.step (w.nodes j) ev).1 → c = c' := by
        intro c c' ho hn
        obtain ⟨hvj, hvf, ht⟩ := hnew v c' t hn
        subst hvj
        obtain ⟨hle, himp⟩ := hold v c t ho
        have := himp ht.symm
        rw [hvf] at this
        exact (Option.some.inj this).symm
      rcases List.mem_append.mp hp₁ with h₁ | h₁ <;>
        rcases List.mem_append.mp hp₂ with h₂ | h₂
      · exact h.unique v c₁ c₂ t h₁ h₂
      · exact key c₁ c₂ h₁ h₂
      · exact (key c₂ c₁ h₂ h₁).symm
      · obtain ⟨_, hv₁, _⟩ := hnew v c₁ t h₁
        obtain ⟨_, hv₂, _⟩ := hnew v c₂ t h₂
        rw [hv₁] at hv₂
        exact Option.some.inj hv₂
    · intro v c t hp
      rw [act_sent] at hp
      rw [act_votes]
      rcases List.mem_append.mp hp with hp' | hp'
      · exact List.mem_append_left _ (h.recorded v c t hp')
      · -- a fresh grant is recorded by construction
        rcases mem_sendsOf hp' with ⟨to, m, heq, hact⟩
        have hvj : v = j := congrArg (fun p => p.1) heq
        have hto : to = c := by have := congrArg (fun p => p.2.1) heq; simpa using this.symm
        have hm : m = Msg.requestVoteResp t true := by
          have := congrArg (fun p => p.2.2) heq; simpa using this.symm
        subst hm; subst hvj
        rcases grant_only_from_requestVote hact with ⟨src, term, candId, li, lt, hevq⟩
        subst hevq
        have hcand := hev src term candId li lt rfl
        rw [Protocol.step] at hact
        obtain ⟨h1, h2, h3, _, _⟩ := handleRequestVote_grant hact
        refine List.mem_append_right _ ?_
        have hvf : (Protocol.step (w.nodes v) (Event.recv src
            (Msg.requestVote term candId li lt))).1.votedFor = some c := by
          rw [Protocol.step, h3, hcand, ← h1, hto]
        have ht : (Protocol.step (w.nodes v) (Event.recv src
            (Msg.requestVote term candId li lt))).1.currentTerm = t := by
          rw [Protocol.step]; exact h2
        rw [← ht]
        exact voteOf_self hvf
    · -- self-votes: the acting node's new vote is recorded; others are unchanged
      intro i c hvf
      rw [act_votes]
      by_cases hij : i = j
      · subst hij
        rw [act_nodes_self] at hvf ⊢
        exact List.mem_append_right _ (voteOf_self hvf)
      · rw [act_nodes_ne _ _ _ hij] at hvf ⊢
        exact List.mem_append_left _ (h.selfRec i c hvf)
  cases hs with
  | deliver src dst m hd hmem =>
      refine main dst _ ?_
      intro src' term candId li lt heq
      have h1 : src = src' := (Event.recv.inj heq).1
      have h2 : m = Msg.requestVote term candId li lt := (Event.recv.inj heq).2
      subst h2; subst h1
      exact hb.rvwf src dst term candId li lt hmem
  | electionTimeout i _ => exact main i _ (fun _ _ _ _ _ hq => Event.noConfusion hq)
  | heartbeat i _ => exact main i _ (fun _ _ _ _ _ hq => Event.noConfusion hq)
  | client i rid cmd _ => exact main i _ (fun _ _ _ _ _ hq => Event.noConfusion hq)

end RaftKV.Proof
