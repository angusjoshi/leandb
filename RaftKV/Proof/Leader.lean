import RaftKV.Proof.Election
import RaftKV.Proof.Quorum
import RaftKV.Proof.VotesChar

/-!
# Election Safety

A leader is a node that collected a quorum of term-`t` votes. `LeaderInv`
records exactly that. Combined with `VoteUnique` — one vote per node per term —
and quorum intersection, at most one node can lead a term.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [KVStore κ]

/--
What it means to have won an election: the node voted for itself, and holds a
duplicate-free quorum of votes, each of which is either its own or is witnessed
by a granted vote on the wire for its current term.
-/
def LeaderInv (members : List Nat) (w : World σ κ) : Prop :=
  ∀ i, (w.nodes i).role = Role.leader →
    (w.nodes i).votedFor = some i
    ∧ (w.nodes i).votesGranted.Nodup
    ∧ (∀ v ∈ (w.nodes i).votesGranted, v ∈ members)
    ∧ (w.nodes i).votesGranted.length ≥ members.length / 2 + 1
    ∧ ∀ v ∈ (w.nodes i).votesGranted,
        v = i ∨ (v, i, Msg.requestVoteResp (w.nodes i).currentTerm true) ∈ w.sent

/-- Every packet on the wire was sent by a cluster member. -/
def SentFrom (members : List Nat) (w : World σ κ) : Prop :=
  ∀ p ∈ w.sent, p.1 ∈ members

/--
The vote bookkeeping of any node that is campaigning or leading: it voted for
itself, its tally is duplicate-free and made of real members, and every vote in
it is either its own or witnessed by a grant on the wire for its current term.

Candidates are included because a leader's tally is inherited from the
candidate it was an instant earlier — the invariant has to hold before the
quorum is reached, or it cannot be established when it is.
-/
def VotesInv (members : List Nat) (w : World σ κ) : Prop :=
  ∀ i, (w.nodes i).role ≠ Role.follower →
    (w.nodes i).votedFor = some i
    ∧ (w.nodes i).votesGranted.Nodup
    ∧ (∀ v ∈ (w.nodes i).votesGranted, v ∈ members)
    ∧ ∀ v ∈ (w.nodes i).votesGranted,
        v = i ∨ (v, i, Msg.requestVoteResp (w.nodes i).currentTerm true) ∈ w.sent

/-- A leader's tally is a quorum. -/
def QuorumInv (members : List Nat) (w : World σ κ) : Prop :=
  ∀ i, (w.nodes i).role = Role.leader →
    (w.nodes i).votesGranted.length ≥ members.length / 2 + 1

/-- `LeaderInv` is exactly `VotesInv` plus `QuorumInv`, restricted to leaders. -/
theorem leaderInv_of {members : List Nat} {w : World σ κ}
    (hv : VotesInv members w) (hq : QuorumInv members w) : LeaderInv members w := by
  intro i hi
  obtain ⟨h1, h2, h3, h4⟩ := hv i (by rw [hi]; exact fun h => Role.noConfusion h)
  exact ⟨h1, h2, h3, hq i hi, h4⟩

/--
**Election Safety.** At most one node leads any term.

Two leaders of term `t` would each hold a quorum of term-`t` votes. Those
quorums intersect, so some node `v` voted for both — but `VoteUnique` says `v`
granted at most one term-`t` vote, and a node's own self-vote is recorded in
`votedFor`, which a leader sets to itself.
-/
theorem electionSafety_of_inv {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hv : VoteInv w) (hu : VoteUnique w) (hl : LeaderInv members w) :
    ElectionSafety w := by
  intro i j t hi hj
  obtain ⟨hir, hit⟩ := hi
  obtain ⟨hjr, hjt⟩ := hj
  obtain ⟨hivote, hind, hisub, hilen, hiwit⟩ := hl i hir
  obtain ⟨hjvote, hjnd, hjsub, hjlen, hjwit⟩ := hl j hjr
  -- Both vote sets are quorums of the same membership.
  let c : Config := { me := i, members := members }
  have hq₁ : IsQuorum c (w.nodes i).votesGranted :=
    ⟨hind, hisub, hilen⟩
  have hq₂ : IsQuorum c (w.nodes j).votesGranted :=
    ⟨hjnd, hjsub, hjlen⟩
  obtain ⟨v, hv₁, hv₂⟩ := quorum_intersect (c := c) hnd hq₁ hq₂
  rcases hiwit v hv₁ with hvi | hvi <;> rcases hjwit v hv₂ with hvj | hvj
  · -- v is both leaders: they are the same node
    exact hvi ▸ hvj ▸ rfl
  · -- v = i voted for j; but i voted for itself
    subst hvi
    rw [hjt] at hvj
    have := (hv v j t hvj).2 (by assumption)
    rw [hivote] at this
    exact (Option.some.inj this)
  · -- symmetric
    subst hvj
    rw [hit] at hvi
    have := (hv v i t hvi).2 (by assumption)
    rw [hjvote] at this
    exact (Option.some.inj this).symm
  · -- v granted a vote to each: one vote per term forces them equal
    rw [hit] at hvi
    rw [hjt] at hvj
    exact hu v i j t hvi hvj

/-! ## Supporting facts -/

theorem sentFrom_act {members : List Nat} {w : World σ κ}
    (h : SentFrom members w) {j : Nat} (hj : j ∈ members) (ev : Event) :
    SentFrom members (w.act j ev) := by
  intro p hp
  rw [act_sent] at hp
  rcases List.mem_append.mp hp with hp' | hp'
  · exact h p hp'
  · rcases mem_sendsOf hp' with ⟨to, m, heq, _⟩
    have : p.1 = j := congrArg (fun q => q.1) heq
    rw [this]; exact hj

/-- Witnesses survive every step, because `sent` only ever grows. -/
theorem witness_mono {w : World σ κ} {j : Nat} {ev : Event} {p : Packet}
    (h : p ∈ w.sent) : p ∈ (w.act j ev).sent := by
  rw [act_sent]; exact List.mem_append_left _ h

/-- `SentFrom` holds initially. -/
theorem sentFrom_init (members : List Nat) :
    SentFrom (σ := σ) (κ := κ) members (World.init members) := by
  intro p hp; simp [World.init] at hp

/-- `VotesInv` and `QuorumInv` hold initially: every node starts as a follower. -/
theorem votesInv_init (members : List Nat) :
    VotesInv (σ := σ) (κ := κ) members (World.init members) := by
  intro i hi; exact absurd rfl hi

theorem quorumInv_init (members : List Nat) :
    QuorumInv (σ := σ) (κ := κ) members (World.init members) := by
  intro i hi; exact Role.noConfusion hi

/-! ## The bookkeeping is inductive -/

/--
**`VotesInv` and `QuorumInv` are preserved by every step.**

By `step_votes_char` there are only two ways to hold a non-follower role after
an event. Starting an election seeds the tally with the node's own self-vote,
which satisfies every conjunct outright. Otherwise the node was already
campaigning or leading, its term is unchanged — so `votedFor_stable` carries its
self-vote across — and its tally either stands still or gains the sender of a
grant that is, by the delivery rule, already on the wire.

`QuorumInv` follows from `step_leader_quorum`: leadership is only ever created
at a site that has just tested `isMajority`.
-/
theorem votes_act {members : List Nat} {w w' : World σ κ}
    (hc : CfgInv members w) (hsf : SentFrom members w)
    (hvi : VotesInv members w) (hqi : QuorumInv members w)
    (hstep : Step members w w') :
    VotesInv members w' ∧ QuorumInv members w' := by
  have main : ∀ (j : Nat), j ∈ members → ∀ (ev : Event),
      (∀ src term, ev = Event.recv src (Msg.requestVoteResp term true) →
        (src, j, Msg.requestVoteResp term true) ∈ w.sent ∧ src ∈ members) →
      VotesInv members (w.act j ev) ∧ QuorumInv members (w.act j ev) := by
    intro j hj ev hdel
    have hmej : (w.nodes j).cfg.me = j := by rw [hc j]
    have hmemj : (w.nodes j).cfg.members = members := by rw [hc j]
    constructor
    · intro i hi
      by_cases hij : i = j
      · subst hij
        rw [act_nodes_self] at hi ⊢
        rcases step_votes_char hi with ⟨hev, hvg, hvf⟩ | ⟨hold, hterm, hvg⟩
        · -- fresh election: the tally is exactly the node's own self-vote
          refine ⟨by rw [hvf, hmej], by rw [hvg]; simp, ?_, ?_⟩
          · intro v hv; rw [hvg, hmej] at hv; rw [List.mem_singleton.mp hv]; exact hj
          · intro v hv; exact Or.inl (by rw [hvg, hmej] at hv; exact List.mem_singleton.mp hv)
        · obtain ⟨h1, h2, h3, h4⟩ := hvi i hold
          have hself : (Protocol.step (w.nodes i) ev).1.votedFor = some i :=
            votedFor_stable _ _ _ hterm h1
          rcases hvg with hvg | ⟨src, term, hev, hterm', hfresh, hvg⟩
          · refine ⟨hself, by rw [hvg]; exact h2, ?_, ?_⟩
            · intro v hv; exact h3 v (by rwa [hvg] at hv)
            · intro v hv
              rw [hterm]
              exact (h4 v (by rwa [hvg] at hv)).imp id witness_mono
          · obtain ⟨hpkt, hsrcm⟩ := hdel src term hev
            refine ⟨hself, ?_, ?_, ?_⟩
            · rw [hvg]; exact List.nodup_cons.mpr ⟨hfresh, h2⟩
            · intro v hv
              rw [hvg] at hv
              rcases List.mem_cons.mp hv with h | h
              · exact h ▸ hsrcm
              · exact h3 v h
            · intro v hv
              rw [hvg] at hv
              rw [hterm]
              rcases List.mem_cons.mp hv with h | h
              · exact Or.inr (h ▸ witness_mono (by rwa [hterm'] at hpkt))
              · exact (h4 v h).imp id witness_mono
      · rw [act_nodes_ne _ _ _ hij] at hi ⊢
        obtain ⟨h1, h2, h3, h4⟩ := hvi i hi
        exact ⟨h1, h2, h3, fun v hv => (h4 v hv).imp id witness_mono⟩
    · intro i hi
      by_cases hij : i = j
      · subst hij
        rw [act_nodes_self] at hi ⊢
        rcases step_leader_quorum hi with ⟨hlead, hvg⟩ | hmaj
        · rw [hvg]; exact hqi i hlead
        · rw [Config.isMajority, Config.quorum, hmemj] at hmaj
          simpa using hmaj
      · rw [act_nodes_ne _ _ _ hij] at hi ⊢; exact hqi i hi
  cases hstep with
  | deliver src dst m hd hmem =>
      refine main dst hd _ ?_
      intro src' term heq
      have h1 : src = src' := (Event.recv.inj heq).1
      have h2 : m = Msg.requestVoteResp term true := (Event.recv.inj heq).2
      subst h2; subst h1
      exact ⟨hmem, hsf _ hmem⟩
  | electionTimeout i hiM => exact main i hiM _ (fun _ _ h => Event.noConfusion h)
  | heartbeat i hiM => exact main i hiM _ (fun _ _ h => Event.noConfusion h)
  | client i rid cmd hiM => exact main i hiM _ (fun _ _ h => Event.noConfusion h)
  | crash i _ =>
      -- a restart comes back a follower, so both claims are vacuous at `i`
      refine ⟨?_, ?_⟩
      · intro v hv
        by_cases heq : v = i
        · subst heq; rw [crash_nodes_self] at hv; exact absurd rfl hv
        · rw [crash_nodes_ne _ _ heq] at hv ⊢
          obtain ⟨h1, h2, h3, h4⟩ := hvi v hv
          exact ⟨h1, h2, h3, fun x hx => (h4 x hx).imp id (fun hq => by rwa [crash_sent])⟩
      · intro v hv
        by_cases heq : v = i
        · subst heq; rw [crash_nodes_self] at hv; exact absurd hv (by simp)
        · rw [crash_nodes_ne _ _ heq] at hv ⊢; exact hqi v hv
  | compact i _ =>
      -- compaction changes no field either invariant mentions
      have hnode : ∀ v, ((w.compactAt i).nodes v).role = (w.nodes v).role
          ∧ ((w.compactAt i).nodes v).votedFor = (w.nodes v).votedFor
          ∧ ((w.compactAt i).nodes v).votesGranted = (w.nodes v).votesGranted
          ∧ ((w.compactAt i).nodes v).currentTerm = (w.nodes v).currentTerm
          ∧ ((w.compactAt i).nodes v).cfg = (w.nodes v).cfg := by
        intro v
        by_cases heq : v = i
        · subst heq; rw [compactAt_nodes_self]; exact ⟨by simp, by simp, by simp, by simp, by simp⟩
        · rw [compactAt_nodes_ne _ _ heq]
          exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · obtain ⟨e1, e2, e3, e4, _⟩ := hnode v
        rw [e1] at hv
        obtain ⟨h1, h2, h3, h4⟩ := hvi v hv
        refine ⟨by rw [e2]; exact h1, by rw [e3]; exact h2, ?_, ?_⟩
        · rw [e3]; exact h3
        · rw [e3, e4, compactAt_sent]; exact h4
      · obtain ⟨e1, _, e3, _, _⟩ := hnode v
        rw [e1] at hv
        rw [e3]
        exact hqi v hv

/-! ## Election Safety, unconditionally -/

/-- Everything needed for Election Safety, maintained together. -/
structure FullInv (members : List Nat) (w : World σ κ) : Prop where
  /-- The vote-accounting invariant of `RaftKV.Proof.Election`. -/
  base : Inv members w
  /-- Packets come from members. -/
  sent : SentFrom members w
  /-- Campaigners and leaders have well-formed tallies. -/
  votes : VotesInv members w
  /-- Leaders' tallies are quorums. -/
  quorum : QuorumInv members w

theorem fullInv_init (members : List Nat) :
    FullInv (σ := σ) (κ := κ) members (World.init members) where
  base := inv_init members
  sent := sentFrom_init members
  votes := votesInv_init members
  quorum := quorumInv_init members

theorem fullInv_step {members : List Nat} {w w' : World σ κ}
    (h : FullInv members w) (hs : Step members w w') : FullInv members w' := by
  have hvq := votes_act h.base.cfg h.sent h.votes h.quorum hs
  refine ⟨inv_step h.base hs, ?_, hvq.1, hvq.2⟩
  cases hs with
  | deliver src dst m hd hmem => exact sentFrom_act h.sent hd _
  | electionTimeout i hiM => exact sentFrom_act h.sent hiM _
  | heartbeat i hiM => exact sentFrom_act h.sent hiM _
  | client i rid cmd hiM => exact sentFrom_act h.sent hiM _
  | crash i _ => intro p hp; rw [crash_sent] at hp; exact h.sent p hp
  | compact i _ => intro p hp; rw [compactAt_sent] at hp; exact h.sent p hp

/-- The full invariant holds in every reachable world. -/
theorem fullInv_reachable {members : List Nat} {w : World σ κ} (h : Reachable members w) :
    FullInv members w := by
  induction h with
  | init => exact fullInv_init members
  | tail _ hs ih => exact fullInv_step ih hs

/--
**Election Safety.**

In every reachable world of a cluster with duplicate-free membership, at most
one node believes it leads any given term — under arbitrary message loss,
reordering, duplication, and interleaving of events across replicas.
-/
theorem electionSafety {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) : ElectionSafety w := by
  have hf := fullInv_reachable h
  exact electionSafety_of_inv hnd hf.base.vote hf.base.unique
    (leaderInv_of hf.votes hf.quorum)

end RaftKV.Proof