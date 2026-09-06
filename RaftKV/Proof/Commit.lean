import RaftKV.Proof.WFLog

/-!
# Commit records and their quorums

The remaining machinery for Leader Completeness:

* snapshots taken into `commits`, `acks` and `elected` are well-formed logs, so
  `wf_matching` applies to them;
* every acknowledgement on the wire has an `acks` record; and
* a leader's `matchIndex` is never invented — a non-zero entry is always backed
  by a real acknowledgement from that peer in the leader's own term.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [LawfulLogStore σ] [KVStore κ]

/-- Well-formedness survives a step, since `created` and `chain` only grow. -/
theorem WellFormedLog.mono {w : World σ κ} {j : Nat} {ev : Event} {lg : σ}
    (h : WellFormedLog w lg) : WellFormedLog (w.act j ev) lg where
  created := fun k e hk => by
    obtain ⟨c, hc⟩ := h.created k e hk; exact ⟨c, created_mono hc⟩
  chained := fun k e hk h2 => by
    obtain ⟨p, hp1, hp2⟩ := h.chained k e hk h2; exact ⟨p, chain_mono hp1, hp2⟩

/-- Every log snapshotted into the ghost records is well formed. -/
def SnapWF (w : World σ κ) : Prop :=
  (∀ L T c lg Q, (L, T, c, lg, Q) ∈ w.commits → WellFormedLog w lg)
    ∧ (∀ p T m lg, (p, T, m, lg) ∈ w.acks → WellFormedLog w lg)
    ∧ (∀ i T lg, (i, T, lg) ∈ w.elected → WellFormedLog w lg)

theorem mem_commitOf {i L T c : Nat} {lg : σ} {Q : List Nat} {pre post : NodeState σ κ}
    (h : (L, T, c, lg, Q) ∈ commitOf i pre post) :
    L = i ∧ T = post.currentTerm ∧ c = post.commitIndex ∧ lg = post.log
      ∧ Q = replicatedOn post post.commitIndex
      ∧ post.role = Role.leader ∧ pre.commitIndex < post.commitIndex := by
  unfold commitOf at h
  split at h
  · rename_i hr
    simp only [List.mem_singleton, Prod.mk.injEq] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, hr.1, hr.2⟩
  · simp at h

/-- A leader's own standing acknowledgement of its whole log. -/
theorem ackOf_self {i : Nat} {s : NodeState σ κ} {acts : List Action}
    (h : s.role = Role.leader) :
    (i, s.currentTerm, LogStore.lastIndex s.log, s.log) ∈ ackOf i s acts := by
  rw [ackOf]
  exact List.mem_append_right _ (by rw [if_pos h]; simp)

/-- The commit record a leader lays down when its commit index moves. -/
theorem mem_commitOf_self {i : Nat} {pre post : NodeState σ κ}
    (hlead : post.role = Role.leader) (hadv : pre.commitIndex < post.commitIndex) :
    (i, post.currentTerm, post.commitIndex, post.log, replicatedOn post post.commitIndex)
      ∈ commitOf i pre post := by
  rw [commitOf, if_pos ⟨hlead, hadv⟩]; simp

/-- The two ways an acknowledgement record arises: a positive reply, or a leader's own log. -/
theorem mem_ackOf_cases {i p T m : Nat} {lg : σ} {s : NodeState σ κ} {acts : List Action}
    (h : (p, T, m, lg) ∈ ackOf i s acts) :
    (∃ to, Action.send to (Msg.appendEntriesResp T true m) ∈ acts ∧ p = i ∧ lg = s.log)
      ∨ (s.role = Role.leader ∧ p = i ∧ T = s.currentTerm
          ∧ m = LogStore.lastIndex s.log ∧ lg = s.log) := by
  rw [ackOf] at h
  rcases List.mem_append.mp h with h | h
  · left
    rcases List.mem_filterMap.mp h with ⟨a, ha, heq⟩
    cases a with
    | reply _ _ _ => simp at heq
    | notLeader _ _ => simp at heq
    | send to msg =>
        cases msg with
        | requestVote a b c d => simp at heq
        | requestVoteResp a b => simp at heq
        | appendEntries a b c d e f => simp at heq
        | appendEntriesResp t2 ok mi =>
            cases ok with
            | false => simp at heq
            | true =>
                simp only [Option.some.injEq, Prod.mk.injEq] at heq
                exact ⟨to, by rw [← heq.2.1, ← heq.2.2.1]; exact ha,
                  heq.1.symm, heq.2.2.2.symm⟩
  · right
    split at h
    · rename_i hlead
      simp only [List.mem_singleton, Prod.mk.injEq] at h
      exact ⟨hlead, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
    · simp at h

theorem mem_ackOf {i p T m : Nat} {lg : σ} {s : NodeState σ κ} {acts : List Action}
    (h : (p, T, m, lg) ∈ ackOf i s acts) : p = i ∧ lg = s.log := by
  rcases mem_ackOf_cases h with ⟨_, _, h1, h2⟩ | ⟨_, h1, _, _, h2⟩
  · exact ⟨h1, h2⟩
  · exact ⟨h1, h2⟩

theorem snapWF_init (members : List Nat) : SnapWF (σ := σ) (κ := κ) (World.init members) := by
  refine ⟨?_, ?_, ?_⟩
  · intro L T c lg Q h; simp [World.init] at h
  · intro p T m lg h; simp [World.init] at h
  · intro i T lg h; simp [World.init] at h

/-- **Snapshot well-formedness is preserved by every step.** -/
theorem snapWF_step {members : List Nat} {w w' : World σ κ}
    (hnd : members.Nodup) (hr : Reachable members w)
    (h : SnapWF w) (hs : Step members w w') : SnapWF w' := by
  have hr' : Reachable members w' := Reachable.tail hr hs
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev → SnapWF w' := by
    intro j ev hw
    subst hw
    have hpost : WellFormedLog (w.act j ev) ((w.act j ev).nodes j).log :=
      wf_node hnd hr' j
    refine ⟨?_, ?_, ?_⟩
    · intro L T c lg Q hmem
      rcases List.mem_append.mp hmem with h' | h'
      · exact (h.1 L T c lg Q h').mono
      · obtain ⟨_, _, _, h4, _, _, _⟩ := mem_commitOf h'
        have hq : ((w.act j ev).nodes j).log = lg := by rw [act_nodes_self]; exact h4.symm
        rw [← hq]; exact hpost
    · intro p T m lg hmem
      rcases List.mem_append.mp hmem with h' | h'
      · exact (h.2.1 p T m lg h').mono
      · obtain ⟨_, h2⟩ := mem_ackOf h'
        have hq : ((w.act j ev).nodes j).log = lg := by rw [act_nodes_self]; exact h2.symm
        rw [← hq]; exact hpost
    · intro i T lg hmem
      rcases List.mem_append.mp hmem with h' | h'
      · exact (h.2.2 i T lg h').mono
      · obtain ⟨_, _, h3, _, _⟩ := mem_electedOf h'
        have hq : ((w.act j ev).nodes j).log = lg := by rw [act_nodes_self]; exact h3.symm
        rw [← hq]; exact hpost
  cases hs with
  | deliver s d m hd hm => exact key d _ rfl
  | electionTimeout k hk => exact key k _ rfl
  | heartbeat k hk => exact key k _ rfl
  | client k rid cmd hk => exact key k _ rfl

theorem snapWF_reachable {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) : SnapWF w := by
  induction h with
  | init => exact snapWF_init members
  | tail hr hs ih => exact snapWF_step hnd hr ih hs

/-! ## Acknowledgements are real -/

/-- Every successful acknowledgement on the wire has a snapshot record. -/
def AckRecorded (w : World σ κ) : Prop :=
  ∀ p d T m, (p, d, Msg.appendEntriesResp T true m) ∈ w.sent →
    ∃ lg, (p, T, m, lg) ∈ w.acks

theorem ackRecorded_init (members : List Nat) :
    AckRecorded (σ := σ) (κ := κ) (World.init members) := by
  intro p d T m h; simp [World.init] at h

theorem ackRecorded_step {members : List Nat} {w w' : World σ κ}
    (h : AckRecorded w) (hs : Step members w w') : AckRecorded w' := by
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev → AckRecorded w' := by
    intro j ev hw
    subst hw
    intro p d T m hp
    rw [act_sent] at hp
    rcases List.mem_append.mp hp with hp' | hp'
    · obtain ⟨lg, hlg⟩ := h p d T m hp'
      exact ⟨lg, List.mem_append_left _ hlg⟩
    · rcases mem_sendsOf hp' with ⟨to, msg, heq, hact⟩
      have hpj : p = j := congrArg (fun q => q.1) heq
      have hm : msg = Msg.appendEntriesResp T true m := by
        have := congrArg (fun q => q.2.2) heq; simpa using this.symm
      subst hm; subst hpj
      refine ⟨(Protocol.step (w.nodes p) ev).1.log, List.mem_append_right _ ?_⟩
      unfold ackOf
      exact List.mem_append_left _
        (List.mem_filterMap.mpr ⟨Action.send to (Msg.appendEntriesResp T true m), hact, rfl⟩)
  cases hs with
  | deliver s d m hd hm => exact key d _ rfl
  | electionTimeout k hk => exact key k _ rfl
  | heartbeat k hk => exact key k _ rfl
  | client k rid cmd hk => exact key k _ rfl

theorem ackRecorded_reachable {members : List Nat} {w : World σ κ} (h : Reachable members w) :
    AckRecorded w := by
  induction h with
  | init => exact ackRecorded_init members
  | tail _ hs ih => exact ackRecorded_step ih hs

/--
**What advancing the commit index guarantees.**

If `advanceCommit` moved the index at all, then the index it chose is strictly
greater than before, carries an entry of the leader's *current* term (Raft's
Figure-8 restriction), and is replicated on a majority according to the leader's
own `matchIndex`.
-/
theorem advanceCommit_spec (s : NodeState σ κ)
    (h : (advanceCommit s).commitIndex ≠ s.commitIndex) :
    (advanceCommit s).commitIndex > s.commitIndex
      ∧ LogStore.termAt s.log (advanceCommit s).commitIndex = some s.currentTerm
      ∧ s.cfg.isMajority (replicatedOn s (advanceCommit s).commitIndex) = true := by
  cases hq : (commitCandidates s).head? with
  | none => exact absurd (by rw [advanceCommit, hq]) h
  | some n =>
      have hci : (advanceCommit s).commitIndex = n := by rw [advanceCommit, hq]
      rw [hci]
      have hmem : n ∈ commitCandidates s := List.mem_of_mem_head? hq
      rw [commitCandidates] at hmem
      have hok : commitOk s n = true :=
        (List.mem_filter.mp (List.mem_reverse.mp hmem)).2
      rw [commitOk] at hok
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
      exact ⟨hok.1.1, hok.1.2, hok.2⟩

/-! ## A leader's `matchIndex` is never invented -/

/--
**Every non-zero `matchIndex` a leader holds is backed by a real acknowledgement
from that peer, in the leader's own term.**

`matchIndex` is written in exactly two places: reset to zero on assuming
leadership, and set from the `matchIndex` field of an `appendEntriesResp` whose
term equals the leader's. So a non-zero value can only have come from a peer
that really did acknowledge that prefix.
-/
def MISound (w : World σ κ) : Prop :=
  ∀ L p, (w.nodes L).role = Role.leader →
    0 < PeerMap.get (w.nodes L).matchIndex p 0 →
    ∃ d, (p, d, Msg.appendEntriesResp (w.nodes L).currentTerm true
            (PeerMap.get (w.nodes L).matchIndex p 0)) ∈ w.sent

theorem miSound_init (members : List Nat) :
    MISound (σ := σ) (κ := κ) (World.init members) := by
  intro L p hlead
  exact absurd hlead (by simp [World.init, Protocol.initState])

/-- Looking up a peer just written gives the written value. -/
theorem pm_get_set_self (m : PeerMap) (k v d : Nat) :
    PeerMap.get (PeerMap.set m k v) k d = v := by
  unfold PeerMap.get PeerMap.set
  simp [List.lookup]

/-- Filtering out a key does not disturb lookups of other keys. -/
private theorem lookup_filter_ne {k k' : Nat} (h : k' ≠ k) :
    ∀ (l : List (Nat × Nat)),
      List.lookup k' (l.filter (fun p => p.1 != k)) = List.lookup k' l := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.filter_cons]
      by_cases hak : a.1 = k
      · have hne : (k' == a.1) = false := by
          simpa using fun hc : k' = a.1 => h (hc.trans hak)
        rw [if_neg (by simp [hak]), ih, List.lookup_cons, hne]
      · rw [if_pos (by simp [hak]), List.lookup_cons, List.lookup_cons, ih]

/-- Looking up a different peer is unaffected by a write. -/
theorem pm_get_set_ne (m : PeerMap) {k k' : Nat} (v d : Nat) (h : k' ≠ k) :
    PeerMap.get (PeerMap.set m k v) k' d = PeerMap.get m k' d := by
  unfold PeerMap.get PeerMap.set
  have hb : (k' == k) = false := by simpa using h
  simp [List.lookup, hb, lookup_filter_ne h m]

/-- Every peer reads back the initial value after `setAll`. -/
theorem pm_get_setAll (ks : List Nat) (k v : Nat) :
    PeerMap.get (PeerMap.setAll ks v) k v = v := by
  unfold PeerMap.get PeerMap.setAll
  induction ks with
  | nil => rfl
  | cons a t ih =>
      by_cases hak : k = a
      · simp [List.lookup, hak]
      · have hb : (k == a) = false := by simpa using hak
        simpa [List.lookup, hb] using ih

/--
**How `matchIndex` can change.**

Exactly three possibilities for a node that is a leader afterwards: the map was
untouched, one peer's entry was set from an acknowledgement in the leader's own
term, or the node has just assumed leadership and every entry reads zero.
-/
theorem step_matchIndex {s : NodeState σ κ} {ev : Event}
    (hl : (Protocol.step s ev).1.role = Role.leader) :
    ((Protocol.step s ev).1.matchIndex = s.matchIndex
        ∧ (Protocol.step s ev).1.currentTerm = s.currentTerm ∧ s.role = Role.leader)
      ∨ (∃ src m, ev = Event.recv src
              (Msg.appendEntriesResp (Protocol.step s ev).1.currentTerm true m)
          ∧ (Protocol.step s ev).1.matchIndex = PeerMap.set s.matchIndex src m
          ∧ (Protocol.step s ev).1.currentTerm = s.currentTerm ∧ s.role = Role.leader)
      ∨ (∀ p, PeerMap.get (Protocol.step s ev).1.matchIndex p 0 = 0) := by
  cases ev with
  | recv src m =>
      cases m with
      | requestVote term candId li lt =>
          left
          rw [Protocol.step, handleRequestVote] at hl ⊢
          by_cases hlt : term < s.currentTerm
          · rw [if_pos hlt] at hl ⊢; exact ⟨rfl, rfl, hl⟩
          · by_cases hgt : term > s.currentTerm
            · exfalso
              rw [if_neg hlt] at hl
              dsimp only at hl
              have hr : (maybeStepDown s term none).1.role = Role.follower := by
                rw [maybeStepDown, if_pos hgt]; rfl
              revert hl; split <;> simp [hr]
            · have hmsd : (maybeStepDown s term none).1 = s := by
                rw [maybeStepDown, if_neg hgt]
              rw [if_neg hlt] at hl ⊢
              dsimp only at hl ⊢
              rw [hmsd] at hl ⊢
              by_cases hg : voteGranted s candId li lt = true
              · rw [if_pos hg] at hl ⊢; exact ⟨rfl, rfl, hl⟩
              · rw [if_neg hg] at hl ⊢; exact ⟨rfl, rfl, hl⟩
      | requestVoteResp term g =>
          rw [Protocol.step, handleRequestVoteResp] at hl ⊢
          by_cases hgt : term > s.currentTerm
          · exfalso; rw [if_pos hgt, stepDown_role] at hl; exact Role.noConfusion hl
          · rw [if_neg hgt] at hl ⊢
            by_cases hguard : s.role != Role.candidate || term != s.currentTerm || !g
            · left; rw [if_pos hguard] at hl ⊢; exact ⟨rfl, rfl, hl⟩
            · right; right
              rw [if_neg hguard] at hl ⊢
              simp only [Bool.not_eq_true, Bool.or_eq_false_iff, bne_eq_false_iff_eq,
                Bool.not_eq_false] at hguard
              dsimp only at hl ⊢
              intro p
              by_cases hmem : s.votesGranted.contains src = true
              · rw [if_pos hmem] at hl ⊢
                by_cases hmaj : s.cfg.isMajority s.votesGranted = true
                · rw [if_pos hmaj]; exact pm_get_setAll _ p 0
                · exfalso; rw [if_neg hmaj] at hl; simp [hguard.1.1] at hl
              · rw [if_neg hmem] at hl ⊢
                by_cases hmaj : s.cfg.isMajority (src :: s.votesGranted) = true
                · rw [if_pos hmaj]; exact pm_get_setAll _ p 0
                · exfalso; rw [if_neg hmaj] at hl; simp [hguard.1.1] at hl
      | appendEntries term l pi pt es lc =>
          left
          rw [Protocol.step, handleAppendEntries] at hl ⊢
          by_cases hlt : term < s.currentTerm
          · rw [if_pos hlt] at hl ⊢; exact ⟨rfl, rfl, hl⟩
          · exfalso
            rw [if_neg hlt] at hl
            dsimp only at hl
            revert hl
            split
            · simp
            · dsimp only; simp
      | appendEntriesResp term ok mi =>
          rw [Protocol.step, handleAppendEntriesResp] at hl ⊢
          by_cases hgt : term > s.currentTerm
          · exfalso; rw [if_pos hgt, stepDown_role] at hl; exact Role.noConfusion hl
          · rw [if_neg hgt] at hl ⊢
            by_cases hguard : s.role != Role.leader || term != s.currentTerm
            · left; rw [if_pos hguard] at hl ⊢; exact ⟨rfl, rfl, hl⟩
            · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hguard
              by_cases hok : ok = true
              · right; left
                rw [if_neg (by simp [hguard.1, hguard.2]), if_pos hok] at hl ⊢
                refine ⟨src, mi, ?_, ?_, ?_, hguard.1⟩
                · rw [show (applyCommitted (advanceCommit
                      { s with matchIndex := PeerMap.set s.matchIndex src mi,
                               nextIndex := PeerMap.set s.nextIndex src (mi + 1) })).1.currentTerm
                      = s.currentTerm by simp, hok, hguard.2]
                · simp
                · first | rfl | simp
              · left
                rw [if_neg (by simp [hguard.1, hguard.2]), if_neg hok] at hl ⊢
                exact ⟨rfl, rfl, hguard.1⟩
  | clientReq rid cmd =>
      left
      rw [Protocol.step, handleClientReq] at hl ⊢
      by_cases hguard : s.role != Role.leader
      · rw [if_pos hguard] at hl ⊢; exact ⟨rfl, rfl, hl⟩
      · rw [if_neg hguard] at hl ⊢
        dsimp only at hl ⊢
        exact ⟨by simp, by simp, by simpa using hguard⟩
  | electionTimeout =>
      rw [Protocol.step] at hl ⊢
      by_cases hlead : s.role == Role.leader
      · left; rw [if_pos hlead] at hl ⊢; exact ⟨rfl, rfl, hl⟩
      · right; right
        rw [if_neg hlead] at hl ⊢
        rw [startElection] at hl ⊢
        dsimp only at hl ⊢
        by_cases hmaj : s.cfg.isMajority [s.cfg.me] = true
        · rw [if_pos hmaj]; intro p; exact pm_get_setAll _ p 0
        · exfalso; rw [if_neg hmaj] at hl; simp at hl
  | heartbeatTimeout =>
      left
      rw [Protocol.step] at hl ⊢
      split at hl
      · rename_i hg; rw [if_pos hg]; exact ⟨rfl, rfl, hl⟩
      · rename_i hg; rw [if_neg hg]; exact ⟨rfl, rfl, hl⟩

/-- **`MISound` is preserved by every step.** -/
theorem miSound_step {members : List Nat} {w w' : World σ κ}
    (h : MISound w) (hs : Step members w w') : MISound w' := by
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev →
      (∀ src m', ev = Event.recv src m' → (src, j, m') ∈ w.sent) →
      MISound w' := by
    intro j ev hw hdel
    subst hw
    intro L p hlead hpos
    by_cases hLj : L = j
    · subst hLj
      rw [act_nodes_self] at hlead hpos ⊢
      rcases step_matchIndex hlead with ⟨hm, ht, hold⟩ | ⟨src, m, hev, hm, ht, hold⟩ | hzero
      · -- nothing was written: the old evidence still applies
        rw [hm] at hpos
        rw [hm, ht]
        obtain ⟨d, hd⟩ := h L p hold hpos
        exact ⟨d, List.mem_append_left _ hd⟩
      · by_cases hps : p = src
        · -- the entry just written, backed by the acknowledgement we handled
          subst hps
          rw [hm, pm_get_set_self] at hpos ⊢
          exact ⟨L, List.mem_append_left _ (hdel p _ hev)⟩
        · rw [hm, pm_get_set_ne _ _ _ hps] at hpos
          rw [hm, pm_get_set_ne _ _ _ hps, ht]
          obtain ⟨d, hd⟩ := h L p hold hpos
          exact ⟨d, List.mem_append_left _ hd⟩
      · exact absurd (hzero p) (by omega)
    · rw [act_nodes_ne _ _ _ hLj] at hlead hpos ⊢
      obtain ⟨d, hd⟩ := h L p hlead hpos
      exact ⟨d, List.mem_append_left _ hd⟩
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

/-- **A leader's `matchIndex` is never invented, in any reachable world.** -/
theorem miSound_reachable {members : List Nat} {w : World σ κ} (h : Reachable members w) :
    MISound w := by
  induction h with
  | init => exact miSound_init members
  | tail _ hs ih => exact miSound_step ih hs

/--
**A leader's replication count is backed by real acknowledgements.**

Combining `miSound_reachable` with `ackRecorded_reachable`: whatever a leader
believes a peer holds, that peer really did acknowledge, and the log it
acknowledged is on permanent record.
-/
theorem matchIndex_ack {members : List Nat} {w : World σ κ}
    (hrch : Reachable members w) {L p : Nat}
    (hlead : (w.nodes L).role = Role.leader)
    (hpos : 0 < PeerMap.get (w.nodes L).matchIndex p 0) :
    ∃ lg, (p, (w.nodes L).currentTerm, PeerMap.get (w.nodes L).matchIndex p 0, lg) ∈ w.acks := by
  obtain ⟨d, hd⟩ := miSound_reachable hrch L p hlead hpos
  exact ackRecorded_reachable hrch p d _ _ hd

/-- The Figure-8 term condition survives `advanceCommit` followed by `applyCommitted`. -/
theorem applyAdvance_term (s : NodeState σ κ)
    (hne : (applyCommitted (advanceCommit s)).1.commitIndex ≠ s.commitIndex) :
    LogStore.termAt (applyCommitted (advanceCommit s)).1.log
        (applyCommitted (advanceCommit s)).1.commitIndex
      = some (applyCommitted (advanceCommit s)).1.currentTerm := by
  have hci : (applyCommitted (advanceCommit s)).1.commitIndex
      = (advanceCommit s).commitIndex := by simp
  have hlog : (applyCommitted (advanceCommit s)).1.log = s.log := by simp
  have hterm : (applyCommitted (advanceCommit s)).1.currentTerm = s.currentTerm := by simp
  rw [hci] at hne ⊢
  rw [hlog, hterm]
  exact (advanceCommit_spec s hne).2.1

/-- The quorum condition survives `advanceCommit` followed by `applyCommitted`. -/
theorem applyAdvance_quorum (s : NodeState σ κ)
    (hne : (applyCommitted (advanceCommit s)).1.commitIndex ≠ s.commitIndex) :
    s.cfg.isMajority (replicatedOn (applyCommitted (advanceCommit s)).1
      (applyCommitted (advanceCommit s)).1.commitIndex) = true := by
  have hci : (applyCommitted (advanceCommit s)).1.commitIndex
      = (advanceCommit s).commitIndex := by simp
  rw [hci] at hne ⊢
  obtain ⟨_, _, hmaj⟩ := advanceCommit_spec s hne
  rw [replicatedOn] at hmaj ⊢
  simpa using hmaj

/--
**Advancing the commit index under leadership means a majority really did have it.**

The only two sites that advance a leader's commit index route through
`advanceCommit`; `handleAppendEntries` also moves it, but demotes to follower
first, so it cannot apply here.
-/
theorem step_commit_quorum {s : NodeState σ κ} {ev : Event}
    (hlead : (Protocol.step s ev).1.role = Role.leader)
    (hadv : s.commitIndex < (Protocol.step s ev).1.commitIndex) :
    s.cfg.isMajority
      (replicatedOn (Protocol.step s ev).1 (Protocol.step s ev).1.commitIndex) = true := by
  cases ev with
  | recv src m =>
      cases m with
      | requestVote term candId li lt =>
          exfalso
          rw [Protocol.step, handleRequestVote] at hadv
          by_cases hlt : term < s.currentTerm
          · rw [if_pos hlt] at hadv; first | exact Nat.lt_irrefl _ hadv | simp at hadv
          · have hmsd : (maybeStepDown s term none).1.commitIndex = s.commitIndex := by
              rw [maybeStepDown]; split <;> rfl
            rw [if_neg hlt] at hadv
            dsimp only at hadv
            revert hadv; split <;> (intro hq; first | exact Nat.lt_irrefl _ (hmsd ▸ hq) | simp [hmsd] at hq)
      | requestVoteResp term g =>
          exfalso
          rw [Protocol.step, handleRequestVoteResp] at hadv
          split at hadv
          · first | exact Nat.lt_irrefl _ hadv | simp at hadv
          · split at hadv
            · first | exact Nat.lt_irrefl _ hadv | simp at hadv
            · dsimp only at hadv; revert hadv; split <;> (split <;> (intro hq; first | exact Nat.lt_irrefl _ hq | simp at hq))
      | appendEntries term l pi pt es lc =>
          exfalso
          rw [Protocol.step, handleAppendEntries] at hlead
          split at hlead
          · rw [Protocol.step, handleAppendEntries, if_pos (by assumption)] at hadv
            simp at hadv
          · dsimp only at hlead; revert hlead; split
            · simp
            · dsimp only; simp
      | appendEntriesResp term ok mi =>
          rw [Protocol.step, handleAppendEntriesResp] at hadv ⊢
          by_cases hgt : term > s.currentTerm
          · exfalso; rw [if_pos hgt] at hadv; first | exact Nat.lt_irrefl _ hadv | simp at hadv
          · rw [if_neg hgt] at hadv ⊢
            by_cases hguard : s.role != Role.leader || term != s.currentTerm
            · exfalso; rw [if_pos hguard] at hadv; first | exact Nat.lt_irrefl _ hadv | simp at hadv
            · rw [if_neg hguard] at hadv ⊢
              by_cases hok : ok = true
              · rw [if_pos hok] at hadv ⊢
                exact applyAdvance_quorum _ (by simp at hadv ⊢; omega)
              · exfalso; rw [if_neg hok] at hadv; first | exact Nat.lt_irrefl _ hadv | simp at hadv
  | clientReq rid cmd =>
      rw [Protocol.step, handleClientReq] at hadv ⊢
      by_cases hguard : s.role != Role.leader
      · exfalso; rw [if_pos hguard] at hadv; first | exact Nat.lt_irrefl _ hadv | simp at hadv
      · rw [if_neg hguard] at hadv ⊢
        dsimp only at hadv ⊢
        exact applyAdvance_quorum _ (by simp at hadv ⊢; omega)
  | electionTimeout =>
      exfalso
      rw [Protocol.step] at hadv
      split at hadv
      · first | exact Nat.lt_irrefl _ hadv | simp at hadv
      · rw [startElection] at hadv; dsimp only at hadv; revert hadv; split <;> (intro hq; first | exact Nat.lt_irrefl _ hq | simp at hq)
  | heartbeatTimeout =>
      exfalso
      rw [Protocol.step] at hadv
      split at hadv <;> exact Nat.lt_irrefl _ hadv

/--
**The committed index carries the leader's own term.**

Raft's Figure-8 restriction, read off the step: a leader only ever advances its
commit index onto an entry of its current term.
-/
theorem commit_term_of_step {s : NodeState σ κ} {ev : Event}
    (hlead : (Protocol.step s ev).1.role = Role.leader)
    (hadv : s.commitIndex < (Protocol.step s ev).1.commitIndex) :
    LogStore.termAt (Protocol.step s ev).1.log (Protocol.step s ev).1.commitIndex
      = some (Protocol.step s ev).1.currentTerm := by
  cases ev with
  | recv src m =>
      cases m with
      | requestVote term candId li lt =>
          exfalso
          rw [Protocol.step, handleRequestVote] at hadv
          by_cases hlt : term < s.currentTerm
          · rw [if_pos hlt] at hadv; exact Nat.lt_irrefl _ hadv
          · have hmsd : (maybeStepDown s term none).1.commitIndex = s.commitIndex := by
              rw [maybeStepDown]; split <;> rfl
            rw [if_neg hlt] at hadv
            dsimp only at hadv
            revert hadv
            split <;> (intro hq; first | exact Nat.lt_irrefl _ (hmsd ▸ hq) | simp [hmsd] at hq)
      | requestVoteResp term g =>
          exfalso
          rw [Protocol.step, handleRequestVoteResp] at hadv
          split at hadv
          · exact Nat.lt_irrefl _ hadv
          · split at hadv
            · exact Nat.lt_irrefl _ hadv
            · dsimp only at hadv; revert hadv
              split <;> (split <;> (intro hq; first | exact Nat.lt_irrefl _ hq | simp at hq))
      | appendEntries term l pi pt es lc =>
          exfalso
          rw [Protocol.step, handleAppendEntries] at hlead
          split at hlead
          · rw [Protocol.step, handleAppendEntries, if_pos (by assumption)] at hadv
            exact Nat.lt_irrefl _ hadv
          · dsimp only at hlead; revert hlead; split
            · simp
            · dsimp only; simp
      | appendEntriesResp term ok mi =>
          rw [Protocol.step, handleAppendEntriesResp] at hadv ⊢
          by_cases hgt : term > s.currentTerm
          · exfalso; rw [if_pos hgt] at hadv; exact Nat.lt_irrefl _ hadv
          · rw [if_neg hgt] at hadv ⊢
            by_cases hguard : s.role != Role.leader || term != s.currentTerm
            · exfalso; rw [if_pos hguard] at hadv; exact Nat.lt_irrefl _ hadv
            · rw [if_neg hguard] at hadv ⊢
              by_cases hok : ok = true
              · rw [if_pos hok] at hadv ⊢
                exact applyAdvance_term _ (by simp at hadv ⊢; omega)
              · exfalso; rw [if_neg hok] at hadv; exact Nat.lt_irrefl _ hadv
  | clientReq rid cmd =>
      rw [Protocol.step, handleClientReq] at hadv ⊢
      by_cases hguard : s.role != Role.leader
      · exfalso; rw [if_pos hguard] at hadv; exact Nat.lt_irrefl _ hadv
      · rw [if_neg hguard] at hadv ⊢
        dsimp only at hadv ⊢
        exact applyAdvance_term _ (by simp at hadv ⊢; omega)
  | electionTimeout =>
      exfalso
      rw [Protocol.step] at hadv
      split at hadv
      · exact Nat.lt_irrefl _ hadv
      · rw [startElection] at hadv; dsimp only at hadv; revert hadv
        split <;> (intro hq; first | exact Nat.lt_irrefl _ hq | simp at hq)
  | heartbeatTimeout =>
      exfalso
      rw [Protocol.step] at hadv
      split at hadv <;> exact Nat.lt_irrefl _ hadv

/-! ## A commit record's quorum is real -/

/--
Every commit record's quorum is a genuine majority of the cluster, and every
member of it other than the leader really did acknowledge that prefix in the
leader's term — with the log it acknowledged on permanent record.
-/
def CommitQuorum (members : List Nat) (w : World σ κ) : Prop :=
  ∀ L T c lg Q, (L, T, c, lg, Q) ∈ w.commits →
    Q.Nodup ∧ (∀ p ∈ Q, p ∈ members) ∧ Q.length ≥ members.length / 2 + 1
      ∧ ∀ p ∈ Q, ∃ m lgp, (p, T, m, lgp) ∈ w.acks ∧ c ≤ m

theorem commitQuorum_init (members : List Nat) :
    CommitQuorum (σ := σ) (κ := κ) members (World.init members) := by
  intro L T c lg Q h; simp [World.init] at h

/-- The quorum a leader counts is duplicate-free and made of members. -/
theorem replicatedOn_ok {s : NodeState σ κ} {members : List Nat} (n : Nat)
    (hm : s.cfg.members = members) (hme : s.cfg.me ∈ members) (hnd : members.Nodup) :
    (replicatedOn s n).Nodup ∧ (∀ p ∈ replicatedOn s n, p ∈ members) := by
  constructor
  · rw [replicatedOn, List.nodup_cons]
    refine ⟨fun hc => Config.peers_ne (List.mem_filter.mp hc).1 rfl, ?_⟩
    refine List.Nodup.sublist List.filter_sublist ?_
    refine List.Nodup.sublist List.filter_sublist ?_
    rw [hm] at *
    exact hnd
  · intro p hp
    rcases List.mem_cons.mp hp with h | h
    · rw [h]; exact hme
    · have h1 := (List.mem_filter.mp h).1
      rw [Config.peers] at h1
      rw [← hm]
      exact (List.mem_filter.mp h1).1


/-- **A commit record's quorum is real, in every reachable world.** -/
theorem commitQuorum_step {members : List Nat} {w w' : World σ κ}
    (hnd : members.Nodup) (hr : Reachable members w)
    (h : CommitQuorum members w) (hs : Step members w w') : CommitQuorum members w' := by
  have hr' : Reachable members w' := Reachable.tail hr hs
  have key : ∀ (j : Nat) (ev : Event), j ∈ members → w' = w.act j ev →
      CommitQuorum members w' := by
    intro j ev hj hw
    subst hw
    intro L T c lg Q hmem
    rcases List.mem_append.mp hmem with h' | h'
    · obtain ⟨h1, h2, h3, h4⟩ := h L T c lg Q h'
      refine ⟨h1, h2, h3, fun p hp => ?_⟩
      obtain ⟨m0, lgp0, hm0, hc0⟩ := h4 p hp
      exact ⟨m0, lgp0, List.mem_append_left _ hm0, hc0⟩
    · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := mem_commitOf h'
      subst e1
      -- everything restated about the post-state as seen through the world
      have hlead : ((w.act L ev).nodes L).role = Role.leader := by
        rw [act_nodes_self]; exact e6
      have hcfg : ((w.act L ev).nodes L).cfg = { me := L, members := members } := by
        rw [act_nodes_self, step_cfg]; exact (allInv_reachable hr).base.cfg L
      have hci : ((w.act L ev).nodes L).commitIndex = c := by
        rw [act_nodes_self]; exact e3.symm
      have hterm : ((w.act L ev).nodes L).currentTerm = T := by
        rw [act_nodes_self]; exact e2.symm
      have hQ : replicatedOn ((w.act L ev).nodes L) c = Q := by
        rw [act_nodes_self, e3]; exact e5.symm
      have hmaj : (w.nodes L).cfg.isMajority
          (replicatedOn ((w.act L ev).nodes L) ((w.act L ev).nodes L).commitIndex) = true := by
        rw [act_nodes_self]; exact step_commit_quorum e6 e7
      have hmembers : ((w.act L ev).nodes L).cfg.members = members := by rw [hcfg]
      have hme : ((w.act L ev).nodes L).cfg.me ∈ members := by rw [hcfg]; exact hj
      obtain ⟨hnd', hsub⟩ := replicatedOn_ok (s := (w.act L ev).nodes L) c hmembers hme hnd
      rw [hQ] at hnd' hsub
      refine ⟨hnd', hsub, ?_, ?_⟩
      · have hc' : (w.nodes L).cfg = { me := L, members := members } :=
          (allInv_reachable hr).base.cfg L
        rw [Config.isMajority, Config.quorum, hc', hci, hQ] at hmaj
        simpa using hmaj
      · intro p hp
        rw [← hQ, replicatedOn, List.mem_cons] at hp
        rcases hp with hp | hp
        · -- the leader's own standing acknowledgement covers it
          have hpL : p = L := by rw [hp, hcfg]
          rw [hpL]
          have hcl : c ≤ LogStore.lastIndex (Protocol.step (w.nodes L) ev).1.log := by
            have hct : LogStore.termAt (Protocol.step (w.nodes L) ev).1.log c
                = some (Protocol.step (w.nodes L) ev).1.currentTerm := by
              rw [e3]; exact commit_term_of_step e6 e7
            unfold LogStore.termAt at hct
            cases hq : LogStore.get (Protocol.step (w.nodes L) ev).1.log c with
            | none => rw [hq] at hct; simp at hct
            | some z => exact ((LogStore.get_isSome_iff _ c).mp (by rw [hq]; rfl)).2
          refine ⟨LogStore.lastIndex (Protocol.step (w.nodes L) ev).1.log,
            (Protocol.step (w.nodes L) ev).1.log, ?_, hcl⟩
          have hself := ackOf_self (i := L) (acts := (Protocol.step (w.nodes L) ev).2) e6
          rw [← e2] at hself
          exact List.mem_append_right _ hself
        · have hge : PeerMap.get ((w.act L ev).nodes L).matchIndex p 0 ≥ c := by
            simpa using (List.mem_filter.mp hp).2
          have hc1 : 1 ≤ c := by omega
          obtain ⟨lgp, hlgp⟩ :=
            matchIndex_ack (L := L) (p := p) hr' hlead (by omega)
          exact ⟨_, lgp, hterm ▸ hlgp, hge⟩
  cases hs with
  | deliver s d m hd hm => exact key d _ hd rfl
  | electionTimeout k hk => exact key k _ hk rfl
  | heartbeat k hk => exact key k _ hk rfl
  | client k rid cmd hk => exact key k _ hk rfl

theorem commitQuorum_reachable {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) : CommitQuorum members w := by
  induction h with
  | init => exact commitQuorum_init members
  | tail hr hs ih => exact commitQuorum_step hnd hr ih hs


/--
**Only a leader, or an `appendEntries` delivery, moves the commit index.**

The two `advanceCommit` call sites sit behind a leadership guard; the follower
path is `handleAppendEntries`. Everything else leaves the index alone.
-/
theorem step_commit_advance {s : NodeState σ κ} {ev : Event}
    (hadv : s.commitIndex < (Protocol.step s ev).1.commitIndex) :
    (Protocol.step s ev).1.role = Role.leader
      ∨ ∃ (src term l pi pt : Nat) (es : List Entry) (lc : Nat),
          ev = Event.recv src (Msg.appendEntries term l pi pt es lc) := by
  cases ev with
  | recv src m =>
      cases m with
      | requestVote term candId li lt =>
          exfalso
          rw [Protocol.step, handleRequestVote] at hadv
          by_cases hlt : term < s.currentTerm
          · rw [if_pos hlt] at hadv; exact Nat.lt_irrefl _ hadv
          · have hmsd : (maybeStepDown s term (none : Option Nat)).1.commitIndex
                = s.commitIndex := by rw [maybeStepDown]; split <;> rfl
            rw [if_neg hlt] at hadv
            dsimp only at hadv
            revert hadv
            split <;> (intro hq; first | exact Nat.lt_irrefl _ (hmsd ▸ hq) | simp [hmsd] at hq)
      | requestVoteResp term g =>
          exfalso
          rw [Protocol.step, handleRequestVoteResp] at hadv
          split at hadv
          · exact Nat.lt_irrefl _ hadv
          · split at hadv
            · exact Nat.lt_irrefl _ hadv
            · dsimp only at hadv; revert hadv
              split <;> (split <;> (intro hq; first | exact Nat.lt_irrefl _ hq | simp at hq))
      | appendEntries term l pi pt es lc => exact Or.inr ⟨src, term, l, pi, pt, es, lc, rfl⟩
      | appendEntriesResp term ok mi =>
          left
          rw [Protocol.step, handleAppendEntriesResp] at hadv ⊢
          by_cases hgt : term > s.currentTerm
          · exfalso; rw [if_pos hgt] at hadv; exact Nat.lt_irrefl _ hadv
          · rw [if_neg hgt] at hadv ⊢
            by_cases hguard : s.role != Role.leader || term != s.currentTerm
            · exfalso; rw [if_pos hguard] at hadv; exact Nat.lt_irrefl _ hadv
            · rw [if_neg hguard] at hadv ⊢
              have hrole : s.role = Role.leader := by
                by_cases hq : s.role = Role.leader
                · exact hq
                · exact absurd (by simp [hq] : (s.role != Role.leader
                    || term != s.currentTerm) = true) hguard
              by_cases hok : ok = true
              · rw [if_pos hok]; simpa using hrole
              · exfalso; rw [if_neg hok] at hadv; exact Nat.lt_irrefl _ hadv
  | clientReq rid cmd =>
      left
      rw [Protocol.step, handleClientReq] at hadv ⊢
      by_cases hguard : s.role != Role.leader
      · exfalso; rw [if_pos hguard] at hadv; exact Nat.lt_irrefl _ hadv
      · rw [if_neg hguard] at hadv ⊢
        dsimp only
        have hrole : s.role = Role.leader := by
          by_cases hq : s.role = Role.leader
          · exact hq
          · exact absurd (by simp [hq] : (s.role != Role.leader) = true) hguard
        simpa using hrole
  | electionTimeout =>
      exfalso
      rw [Protocol.step] at hadv
      split at hadv
      · exact Nat.lt_irrefl _ hadv
      · rw [startElection] at hadv; dsimp only at hadv; revert hadv
        split <;> (intro hq; first | exact Nat.lt_irrefl _ hq | simp at hq)
  | heartbeatTimeout =>
      exfalso
      rw [Protocol.step] at hadv
      split at hadv <;> exact Nat.lt_irrefl _ hadv

end RaftKV.Proof
