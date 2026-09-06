import RaftKV.Proof.Votes

/-!
# The vote invariant, and vote uniqueness

The inductive invariant that makes elections safe. Four conjuncts, maintained
together because each needs the others:

* `CfgInv` — every node knows its own id and the membership.
* `RvWf` — a `requestVote` on the wire names its sender as the candidate.
* `VoteInv` — a granted vote for term `t` is backed by the voter's own state:
  its term has reached `t`, and while it is still *at* `t`, its `votedFor`
  still names the node it voted for.
* `VoteUnique` — **a node grants at most one vote per term.**

`VoteUnique` is the payload; the other three exist to make it inductive.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [KVStore κ]

/-! ## Rewriting lemmas for `World.act` -/

theorem act_nodes_ne (w : World σ κ) (j : Nat) (ev : Event) {i : Nat} (h : i ≠ j) :
    (w.act j ev).nodes i = w.nodes i := by
  rw [World.act]; dsimp only; rw [if_neg h]

theorem act_nodes_self (w : World σ κ) (j : Nat) (ev : Event) :
    (w.act j ev).nodes j = (Protocol.step (w.nodes j) ev).1 := by
  rw [World.act]; dsimp only; rw [if_pos rfl]

/-- The ghost logical log of the acting node takes the same operation its log did. -/
theorem act_full_self (w : World σ κ) (j : Nat) (ev : Event) :
    (w.act j ev).full j = fullStep w j ev := by
  rw [World.act]; dsimp only; rw [if_pos rfl]

/-- And no other node's logical log moves. -/
theorem act_full_ne (w : World σ κ) (j : Nat) {i : Nat} (ev : Event) (h : i ≠ j) :
    (w.act j ev).full i = w.full i := by
  rw [World.act]; dsimp only; rw [if_neg h]

@[simp] theorem crash_full (w : World σ κ) (i : Nat) : (w.crash i).full = w.full := rfl

theorem act_sent (w : World σ κ) (j : Nat) (ev : Event) :
    (w.act j ev).sent = w.sent ++ sendsOf j (Protocol.step (w.nodes j) ev).2 := rfl

/-! ## The invariant -/

/-- Every node's configuration names itself and the agreed membership. -/
def CfgInv (members : List Nat) (w : World σ κ) : Prop :=
  ∀ i, (w.nodes i).cfg = { me := i, members := members }

/-- A `requestVote` in flight always names its sender as the candidate. -/
def RvWf (w : World σ κ) : Prop :=
  ∀ i j t c li lt, (i, j, Msg.requestVote t c li lt) ∈ w.sent → c = i

/-- A granted vote is backed by the voter's recorded state. -/
def VoteInv (w : World σ κ) : Prop :=
  ∀ v c t, (v, c, Msg.requestVoteResp t true) ∈ w.sent →
    t ≤ (w.nodes v).currentTerm
      ∧ ((w.nodes v).currentTerm = t → (w.nodes v).votedFor = some c)

/-- **One vote per node per term.** -/
def VoteUnique (w : World σ κ) : Prop :=
  ∀ v c₁ c₂ t, (v, c₁, Msg.requestVoteResp t true) ∈ w.sent →
               (v, c₂, Msg.requestVoteResp t true) ∈ w.sent → c₁ = c₂

/-- The four conjuncts, maintained together. -/
structure Inv (members : List Nat) (w : World σ κ) : Prop where
  /-- Configurations are correct and immutable. -/
  cfg : CfgInv members w
  /-- Vote requests are well-formed. -/
  rvwf : RvWf w
  /-- Grants are backed by voter state. -/
  vote : VoteInv w
  /-- At most one grant per voter per term. -/
  unique : VoteUnique w

/-! ## The invariant holds initially -/

theorem inv_init (members : List Nat) : Inv (σ := σ) (κ := κ) members (World.init members) where
  cfg := by intro i; rfl
  rvwf := by intro i j t c li lt h; simp [World.init] at h
  vote := by intro v c t h; simp [World.init] at h
  unique := by intro v c₁ c₂ t h; simp [World.init] at h

/-! ## Preservation -/

theorem cfg_act {members : List Nat} {w : World σ κ} (h : CfgInv members w) (j : Nat) (ev : Event) :
    CfgInv members (w.act j ev) := by
  intro i
  by_cases hij : i = j
  · subst hij; rw [act_nodes_self, step_cfg]; exact h i
  · rw [act_nodes_ne _ _ _ hij]; exact h i

theorem rvwf_act {members : List Nat} {w : World σ κ}
    (hc : CfgInv members w) (h : RvWf w) (j : Nat) (ev : Event) :
    RvWf (w.act j ev) := by
  intro i j' t c li lt hp
  rw [act_sent] at hp
  rcases List.mem_append.mp hp with hp' | hp'
  · exact h i j' t c li lt hp'
  · rcases mem_sendsOf hp' with ⟨to, m, heq, hact⟩
    have hi : i = j := congrArg (fun p => p.1) heq
    have hm : m = Msg.requestVote t c li lt := by
      have := congrArg (fun p => p.2.2) heq; simpa using this.symm
    subst hm
    have := step_requestVote_cid hact
    rw [hc j] at this
    simpa [hi] using this

/--
The heart of the induction: a fresh grant cannot contradict an existing one.

If node `j` grants a vote for term `t`, then `t` is exactly `j`'s new term. Any
earlier grant for `t` forces `j`'s term to have *already* been `t`, hence `j`
had already recorded a `votedFor` — and the grant guard refuses to overwrite it
with a different candidate.
-/
theorem vote_act {members : List Nat} {w w' : World σ κ}
    (hc : CfgInv members w) (hr : RvWf w) (hv : VoteInv w) (hu : VoteUnique w)
    (hstep : Step members w w') :
    VoteInv w' ∧ VoteUnique w' := by
  -- Reduce every rule to a single `act`, remembering the delivered packet.
  have main : ∀ (j : Nat) (ev : Event),
      (∀ src term candId li lt, ev = Event.recv src (Msg.requestVote term candId li lt) →
        candId = src) →
      VoteInv (w.act j ev) ∧ VoteUnique (w.act j ev) := by
    intro j ev hev
    -- How a grant packet in the new world arises.
    have grant_new : ∀ (v c t : Nat),
        (v, c, Msg.requestVoteResp t true) ∈ sendsOf j (Protocol.step (w.nodes j) ev).2 →
        v = j ∧ ((w.act j ev).nodes j).currentTerm = t
          ∧ ((w.act j ev).nodes j).votedFor = some c := by
      intro v c t hp
      rcases mem_sendsOf hp with ⟨to, m, heq, hact⟩
      have hv' : v = j := congrArg (fun p => p.1) heq
      have hto : to = c := by have := congrArg (fun p => p.2.1) heq; simpa using this.symm
      have hm : m = Msg.requestVoteResp t true := by
        have := congrArg (fun p => p.2.2) heq; simpa using this.symm
      subst hm; subst hto
      rcases grant_only_from_requestVote hact with ⟨src, term, candId, li, lt, hevq⟩
      subst hevq
      have hcand := hev src term candId li lt rfl
      rw [Protocol.step] at hact
      rcases handleRequestVote_grant hact with ⟨h1, h2, h3, _, _⟩
      refine ⟨hv', ?_, ?_⟩
      · rw [act_nodes_self, Protocol.step]; exact h2
      · rw [act_nodes_self, Protocol.step, h3, hcand, h1]
    constructor
    · -- VoteInv
      intro v c t hp
      rw [act_sent] at hp
      rcases List.mem_append.mp hp with hp' | hp'
      · -- an old packet: the voter's term only rose
        obtain ⟨hle, himp⟩ := hv v c t hp'
        by_cases hvj : v = j
        · subst hvj
          rw [act_nodes_self]
          refine ⟨Nat.le_trans hle (step_term_mono _ _), ?_⟩
          intro heq
          have hold : (w.nodes v).currentTerm = t :=
            Nat.le_antisymm (heq ▸ step_term_mono (w.nodes v) ev) hle
          exact votedFor_stable _ _ _ (by rw [heq, hold]) (himp hold)
        · rw [act_nodes_ne _ _ _ hvj]; exact ⟨hle, himp⟩
      · -- a fresh grant
        obtain ⟨hvj, ht, hvf⟩ := grant_new v c t hp'
        subst hvj
        exact ⟨Nat.le_of_eq ht.symm, fun _ => hvf⟩
    · -- VoteUnique
      intro v c₁ c₂ t hp₁ hp₂
      rw [act_sent] at hp₁ hp₂
      -- A fresh grant pins down the voter's post-state completely.
      have key : ∀ c c', (v, c, Msg.requestVoteResp t true) ∈ w.sent →
          (v, c', Msg.requestVoteResp t true) ∈ sendsOf j (Protocol.step (w.nodes j) ev).2 →
          c = c' := by
        intro c c' hold hnew
        obtain ⟨hvj, ht, hvf⟩ := grant_new v c' t hnew
        subst hvj
        obtain ⟨hle, himp⟩ := hv v c t hold
        rw [act_nodes_self] at ht hvf
        have hold' : (w.nodes v).currentTerm = t :=
          Nat.le_antisymm (ht ▸ step_term_mono (w.nodes v) ev) hle
        have hstab := votedFor_stable (w.nodes v) ev c (by rw [ht, hold']) (himp hold')
        rw [hvf] at hstab
        exact (Option.some.inj hstab).symm
      rcases List.mem_append.mp hp₁ with h₁ | h₁ <;>
        rcases List.mem_append.mp hp₂ with h₂ | h₂
      · exact hu v c₁ c₂ t h₁ h₂
      · exact key c₁ c₂ h₁ h₂
      · exact (key c₂ c₁ h₂ h₁).symm
      · obtain ⟨_, ht₁, hv₁⟩ := grant_new v c₁ t h₁
        obtain ⟨_, _, hv₂⟩ := grant_new v c₂ t h₂
        rw [hv₁] at hv₂
        exact Option.some.inj hv₂
  cases hstep with
  | deliver src dst m _ hmem =>
      refine main dst (.recv src m) ?_
      intro src' term candId li lt heq
      have h1 : src = src' := (Event.recv.inj heq).1
      have h2 : m = Msg.requestVote term candId li lt := (Event.recv.inj heq).2
      subst h2
      subst h1
      exact hr src dst term candId li lt hmem
  | electionTimeout i _ => exact main i _ (fun _ _ _ _ _ h => Event.noConfusion h)
  | heartbeat i _ => exact main i _ (fun _ _ _ _ _ h => Event.noConfusion h)
  | client i rid cmd _ => exact main i _ (fun _ _ _ _ _ h => Event.noConfusion h)
  | crash i _ =>
      -- persistence is exactly what makes this survive: `currentTerm` and
      -- `votedFor` are the durable fields, and `sent` never moves
      refine ⟨?_, ?_⟩
      · intro v c t hp
        rw [crash_sent] at hp
        obtain ⟨hle, himp⟩ := hv v c t hp
        by_cases hvi : v = i
        · subst hvi; rw [crash_nodes_self]; simpa using And.intro hle himp
        · rw [crash_nodes_ne _ _ hvi]; exact ⟨hle, himp⟩
      · intro v c₁ c₂ t h₁ h₂
        rw [crash_sent] at h₁ h₂
        exact hu v c₁ c₂ t h₁ h₂
  | compact i _ =>
      -- compaction touches only the log; terms, votes and `sent` are untouched
      refine ⟨?_, ?_⟩
      · intro v c t hp
        rw [compactAt_sent] at hp
        obtain ⟨hle, himp⟩ := hv v c t hp
        by_cases hvi : v = i
        · subst hvi; rw [compactAt_nodes_self]; simpa using And.intro hle himp
        · rw [compactAt_nodes_ne _ _ hvi]; exact ⟨hle, himp⟩
      · intro v c₁ c₂ t h₁ h₂
        rw [compactAt_sent] at h₁ h₂
        exact hu v c₁ c₂ t h₁ h₂
/-- The invariant is preserved by every step. -/
theorem inv_step {members : List Nat} {w w' : World σ κ}
    (h : Inv members w) (hs : Step members w w') : Inv members w' := by
  have hvu := vote_act h.cfg h.rvwf h.vote h.unique hs
  cases hs with
  | deliver src dst m hd hmem =>
      exact ⟨cfg_act h.cfg _ _, rvwf_act h.cfg h.rvwf _ _, hvu.1, hvu.2⟩
  | electionTimeout i hi =>
      exact ⟨cfg_act h.cfg _ _, rvwf_act h.cfg h.rvwf _ _, hvu.1, hvu.2⟩
  | heartbeat i hi =>
      exact ⟨cfg_act h.cfg _ _, rvwf_act h.cfg h.rvwf _ _, hvu.1, hvu.2⟩
  | client i rid cmd hi =>
      exact ⟨cfg_act h.cfg _ _, rvwf_act h.cfg h.rvwf _ _, hvu.1, hvu.2⟩
  | crash i hi =>
      refine ⟨?_, ?_, hvu.1, hvu.2⟩
      · intro j
        by_cases hji : j = i
        · subst hji; rw [crash_nodes_self, restart_cfg]; exact h.cfg j
        · rw [crash_nodes_ne _ _ hji]; exact h.cfg j
      · intro a b t c li lt hp; rw [crash_sent] at hp; exact h.rvwf a b t c li lt hp
  | compact i hi =>
      refine ⟨?_, ?_, hvu.1, hvu.2⟩
      · intro j
        by_cases hji : j = i
        · subst hji; rw [compactAt_nodes_self, compactTo_cfg]; exact h.cfg j
        · rw [compactAt_nodes_ne _ _ hji]; exact h.cfg j
      · intro a b t c li lt hp; rw [compactAt_sent] at hp; exact h.rvwf a b t c li lt hp
/-- **The invariant holds in every reachable world.** -/
theorem inv_reachable {members : List Nat} {w : World σ κ} (h : Reachable members w) :
    Inv members w := by
  induction h with
  | init => exact inv_init members
  | tail _ hs ih => exact inv_step ih hs

/--
**One vote per term.** In any reachable world, a node never has two granted
votes for the same term on the wire to different candidates.
-/
theorem vote_uniqueness {members : List Nat} {w : World σ κ} (h : Reachable members w) :
    VoteUnique w := (inv_reachable h).unique

end RaftKV.Proof
