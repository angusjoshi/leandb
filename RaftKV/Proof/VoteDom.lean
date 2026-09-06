import RaftKV.Proof.Commit

/-!
# A vote means the candidate's log dominates the voter's

The `upToDate` check is the only thing standing between Raft and a leader that
has lost committed entries. This module makes it say something durable:

> If `v` granted `c` a vote in term `U`, and `c` was elected in `U` with log
> `lg`, then `lg` is at least as up to date as `v`'s log was at that instant —
> a strictly later last term, or the same last term and at least as many
> entries.

Every link in that chain is now available: the grant's guard
(`handleRequestVote_grant`), the fact that a `requestVote` advertises the
sender's real log (`step_requestVote_log`), and the fact that the advertised log
is the elected one (`rvElected_reachable`).
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [LawfulLogStore σ] [KVStore κ]

theorem act_voteLogs (w : World σ κ) (j : Nat) (ev : Event) :
    (w.act j ev).voteLogs
      = w.voteLogs ++ voteLogOf j (Protocol.step (w.nodes j) ev).1
          (Protocol.step (w.nodes j) ev).2 := rfl

theorem voteLog_mono {w : World σ κ} {j : Nat} {ev : Event} {v U : Nat} {lg : σ}
    (h : (v, U, lg) ∈ w.voteLogs) : (v, U, lg) ∈ (w.act j ev).voteLogs := by
  rw [act_voteLogs]; exact List.mem_append_left _ h

/--
Every vote-log record is backed by the grant that produced it: the voter really
did answer a `requestVote` whose advertised log passed its `upToDate` check.
-/
def VoteDom (w : World σ κ) : Prop :=
  ∀ v U (lgv : σ), (v, U, lgv) ∈ w.voteLogs →
    ∃ c li lt, (c, v, Msg.requestVote U c li lt) ∈ w.sent
      ∧ (v, c, U) ∈ w.votes
      ∧ (lt > LogStore.lastTerm lgv ∨ (lt = LogStore.lastTerm lgv
          ∧ li ≥ LogStore.lastIndex lgv))

theorem voteDom_init (members : List Nat) :
    VoteDom (σ := σ) (κ := κ) (World.init members) := by
  intro v U lgv h; simp [World.init] at h

/-- **`VoteDom` is preserved by every step.** -/
theorem voteDom_step {members : List Nat} {w w' : World σ κ}
    (hb : Inv members w) (h : VoteDom w) (hs : Step members w w') : VoteDom w' := by
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev →
      (∀ src m', ev = Event.recv src m' → (src, j, m') ∈ w.sent) →
      VoteDom w' := by
    intro j ev hw hdel
    subst hw
    intro v U lgv hmem
    rw [act_voteLogs] at hmem
    rcases List.mem_append.mp hmem with h' | h'
    · obtain ⟨c, li, lt, h1, h2, h3⟩ := h v U lgv h'
      exact ⟨c, li, lt, List.mem_append_left _ h1, List.mem_append_left _ h2, h3⟩
    · -- a fresh grant: read the guard off `handleRequestVote`
      unfold voteLogOf at h'
      rcases List.mem_filterMap.mp h' with ⟨a, ha, heq⟩
      cases a with
      | reply _ _ => simp at heq
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
                  obtain ⟨hv, hU, hlg⟩ := heq
                  subst hv; subst hU; subst hlg
                  rcases grant_only_from_requestVote ha with
                    ⟨src, term, candId, li, lt, hev⟩
                  subst hev
                  have hpkt := hdel src (Msg.requestVote term candId li lt) rfl
                  have hcand : candId = src :=
                    hb.rvwf src j term candId li lt hpkt
                  rw [Protocol.step] at ha
                  obtain ⟨h1, h2, h3, h4, h5⟩ := handleRequestVote_grant ha
                  refine ⟨candId, li, lt, ?_, ?_, ?_⟩
                  · rw [hcand] at hpkt
                    rw [hcand, h5]; exact List.mem_append_left _ hpkt
                  · rw [act_votes]
                    refine List.mem_append_right _ ?_
                    have hvf : (Protocol.step (w.nodes j)
                        (Event.recv src (Msg.requestVote term candId li lt))).1.votedFor
                        = some candId := by rw [Protocol.step]; exact h3
                    have ht : (Protocol.step (w.nodes j)
                        (Event.recv src (Msg.requestVote term candId li lt))).1.currentTerm
                        = t := by rw [Protocol.step]; exact h2
                    rw [← ht]
                    exact voteOf_self hvf
                  · -- the guard is exactly the domination condition
                    rw [upToDate] at h4
                    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
                      beq_iff_eq] at h4
                    rcases h4 with hgt | ⟨heq1, hge⟩
                    · exact Or.inl (by simpa [Protocol.step] using hgt)
                    · exact Or.inr ⟨by simpa [Protocol.step] using heq1,
                                     by simpa [Protocol.step] using hge⟩
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

theorem voteDom_reachable {members : List Nat} {w : World σ κ} (h : Reachable members w) :
    VoteDom w := by
  induction h with
  | init => exact voteDom_init members
  | tail hr hs ih => exact voteDom_step (inv_reachable hr) ih hs

/--
**A vote means the elected leader's log dominates the voter's.**

The `upToDate` guard, made durable: whoever wins term `U` was elected with a log
at least as up to date as the log every one of its voters held when it voted.
-/
theorem vote_dominates {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) {v c U : Nat} {lgv lg : σ}
    (hvl : (v, U, lgv) ∈ w.voteLogs) (hvote : (v, c, U) ∈ w.votes)
    (hel : (c, U, lg) ∈ w.elected) :
    LogStore.lastTerm lg > LogStore.lastTerm lgv
      ∨ (LogStore.lastTerm lg = LogStore.lastTerm lgv
          ∧ LogStore.lastIndex lg ≥ LogStore.lastIndex lgv) := by
  obtain ⟨c', li, lt, hpkt, hv', hdom⟩ := voteDom_reachable hrch v U lgv hvl
  -- the voter voted only once in this term, so `c' = c`
  have hcc : c' = c :=
    (allInv_reachable hrch).ghost.unique v c' c U hv' hvote
  subst hcc
  obtain ⟨hli, hlt⟩ := rvElected_reachable hnd hrch c' v U c' li lt lg hpkt hel
  rw [hli, hlt] at hdom
  exact hdom

end RaftKV.Proof
