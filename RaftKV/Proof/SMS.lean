import RaftKV.Proof.LC

/-!
# State Machine Safety

The last of Raft's four safety properties: two replicas never apply different
entries at the same log index.

The argument has two halves. The first is combinatorial and already done: an
entry committed in a term is present in every later leader's log
(`leaderCompleteness`), so **at most one entry is ever committed at an index**
(`committed_unique`). The second is the bookkeeping that connects a replica's
`lastApplied` to that notion of commitment:

* `AppliedBound` — the state machine never runs past `commitIndex`;
* `CommitBound` — `commitIndex` is always inside the log;
* `MsgCommitted` — what a leader advertises as committed really is committed;
* `AppliedCommitted` — everything a replica considers committed is committed.

The last three are mutually dependent — a follower learns of commitment from a
message, and a leader's message is justified by its own belief — so they are
carried as one invariant.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [LawfulLogStore σ] [KVStore κ]

/-! ## At most one entry is ever committed at an index -/

theorem committed_mono {w : World σ κ} {j : Nat} {ev : Event} {idx T : Nat} {e : Entry}
    (h : Protocol.Committed w idx e T) : Protocol.Committed (w.act j ev) idx e T := by
  obtain ⟨L, c, lg, Q, hc, h1, h2⟩ := h
  exact ⟨L, c, lg, Q, List.mem_append_left _ hc, h1, h2⟩

theorem committed_crash_mono {w : World σ κ} {i : Nat} {idx T : Nat} {e : Entry}
    (h : Protocol.Committed w idx e T) : Protocol.Committed (w.crash i) idx e T := by
  obtain ⟨L, c, lg, Q, hc, h1, h2⟩ := h
  exact ⟨L, c, lg, Q, by rw [crash_commits]; exact hc, h1, h2⟩

/-- **A committed index determines its entry.** -/
theorem committed_unique {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) {idx T₁ T₂ : Nat} {e₁ e₂ : Entry}
    (h₁ : Protocol.Committed w idx e₁ T₁) (h₂ : Protocol.Committed w idx e₂ T₂) :
    e₁ = e₂ := by
  -- the ordered case, then symmetry
  have key : ∀ (S₁ S₂ : Nat) (f₁ f₂ : Entry), S₁ ≤ S₂ →
      Protocol.Committed w idx f₁ S₁ → Protocol.Committed w idx f₂ S₂ → f₁ = f₂ := by
    intro S₁ S₂ f₁ f₂ hle g₁ g₂
    obtain ⟨L₁, c₁, lg₁, Q₁, hc₁, hi₁, hg₁⟩ := g₁
    obtain ⟨L₂, c₂, lg₂, Q₂, hc₂, hi₂, hg₂⟩ := g₂
    obtain ⟨hcT₁, hL₁⟩ := commit_ack_quorum hnd hrch hc₁
    obtain ⟨hcT₂, hL₂⟩ := commit_ack_quorum hnd hrch hc₂
    obtain ⟨hQ1, hQ2, hQ3, hQ4⟩ := commitQuorum_reachable hnd hrch L₁ S₁ c₁ lg₁ Q₁ hc₁
    have hc₁len : c₁ ≤ LogStore.lastIndex lg₁ := by
      unfold LogStore.termAt at hcT₁
      cases hq : LogStore.get lg₁ c₁ with
      | none => rw [hq] at hcT₁; simp at hcT₁
      | some z => exact ((LogStore.get_isSome_iff lg₁ c₁).mp (by rw [hq]; rfl)).2
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · -- the same term: two snapshots of one leader
      subst heq
      have hled₁ : (L₁, S₁) ∈ w.led := (llInv_reachable hnd hrch).led L₁ S₁ lg₁ hL₁
      have hled₂ : (L₂, S₁) ∈ w.led := (llInv_reachable hnd hrch).led L₂ S₁ lg₂ hL₂
      have : L₂ = L₁ := led_unique hnd hrch hled₂ hled₁
      subst this
      rcases (llInv_reachable hnd hrch).chain L₂ S₁ lg₁ lg₂ hL₁ hL₂ with hp | hp
      · have hq := hp idx (by omega)
        rw [hg₁] at hq; rw [hq] at hg₂; exact Option.some.inj hg₂
      · have hc₂len : c₂ ≤ LogStore.lastIndex lg₂ := by
          unfold LogStore.termAt at hcT₂
          cases hq : LogStore.get lg₂ c₂ with
          | none => rw [hq] at hcT₂; simp at hcT₂
          | some z => exact ((LogStore.get_isSome_iff lg₂ c₂).mp (by rw [hq]; rfl)).2
        have hq := hp idx (by omega)
        rw [hg₂] at hq; rw [hq] at hg₁; exact (Option.some.inj hg₁).symm
    · -- a strictly later term: leader completeness carries the entry
      have hagree : AgreeUpTo lg₂ lg₁ c₁ :=
        lc_aux hnd hrch hL₁ hcT₁ ⟨Q₁, hQ1, hQ2, hQ3, hQ4⟩ S₂ L₂ S₂ lg₂ hL₂ hlt (Nat.le_refl _)
      have hq := hagree idx hi₁
      rw [hg₂] at hq; rw [← hq] at hg₁; exact (Option.some.inj hg₁).symm
  rcases Nat.le_total T₁ T₂ with hle | hle
  · exact key T₁ T₂ e₁ e₂ hle h₁ h₂
  · exact (key T₂ T₁ e₂ e₁ hle h₂ h₁).symm

/-! ## The state machine never runs past the commit index -/

def AppliedBound (w : World σ κ) : Prop :=
  ∀ i, (w.nodes i).lastApplied ≤ (w.nodes i).commitIndex

theorem appliedBound_reachable {members : List Nat} {w : World σ κ}
    (h : Reachable members w) : AppliedBound w := by
  induction h with
  | init => intro i; simp [World.init, Protocol.initState]
  | @tail w0 w1 hr hs ih =>
      have key : ∀ (j : Nat) (ev : Event), w1 = w0.act j ev → AppliedBound w1 := by
        intro j ev hw
        subst hw
        intro i
        by_cases hij : i = j
        · subst hij; rw [act_nodes_self]; exact step_applied_le _ _ (ih i)
        · rw [act_nodes_ne _ _ _ hij]; exact ih i
      cases hs with
      | deliver s d m hd hm => exact key d _ rfl
      | electionTimeout k hk => exact key k _ rfl
      | heartbeat k hk => exact key k _ rfl
      | client k rid cmd hk => exact key k _ rfl
      | crash k hk =>
          intro i
          by_cases hik : i = k
          · subst hik; rw [crash_nodes_self, restart_lastApplied, restart_commitIndex]
            exact Nat.le_refl _
          · rw [crash_nodes_ne _ _ hik]; exact ih i


/-! ## Commitment bookkeeping -/

/-- A node's commit index always points inside its own log. -/
def CommitBound (w : World σ κ) : Prop :=
  ∀ i, (w.nodes i).commitIndex ≤ LogStore.lastIndex (w.full i)

/-- What a leader advertises as committed really is committed. -/
def MsgCommitted (w : World σ κ) : Prop :=
  ∀ (src dst t l pi pt : Nat) (es : List Entry) (lc : Nat),
    (src, dst, Msg.appendEntries t l pi pt es lc) ∈ w.sent →
    ∃ lgM : σ, (src, t, lgM) ∈ w.leaderLogs ∧ lc ≤ LogStore.lastIndex lgM
      ∧ (∀ (n : Nat) (e : Entry), es[n]? = some e →
          LogStore.get lgM (pi + 1 + n) = some e)
      ∧ (LogStore.termAt lgM pi).getD 0 = pt
      ∧ es.length = LogStore.lastIndex lgM - pi
      ∧ ∀ k (e : Entry), k ≤ lc → LogStore.get lgM k = some e →
          ∃ T', Protocol.Committed w k e T' ∧ T' ≤ t

/-- Everything a node believes committed really is committed. -/
def AppliedCommitted (w : World σ κ) : Prop :=
  ∀ i k (e : Entry), k ≤ (w.nodes i).commitIndex → LogStore.get (w.full i) k = some e →
    ∃ T', Protocol.Committed w k e T' ∧ T' ≤ (w.nodes i).currentTerm

/-- The three commitment invariants, which have to be carried together. -/
structure SInv (members : List Nat) (w : World σ κ) : Prop where
  /-- The commit index is inside the log. -/
  bound : CommitBound w
  /-- Advertised commitment is real. -/
  msg : MsgCommitted w
  /-- Believed commitment is real. -/
  cov : AppliedCommitted w

theorem sInv_init (members : List Nat) : SInv (σ := σ) (κ := κ) members (World.init members) where
  bound := by intro i; simp [World.init, Protocol.initState]
  msg := by intro src dst t l pi pt es lc h; simp [World.init] at h
  cov := by
    intro i k e hk hget
    exfalso
    have h0 : k = 0 := by
      simp [World.init, Protocol.initState] at hk
      omega
    rw [h0] at hget
    simp [World.init, Protocol.initState] at hget


/--
**A splice never disturbs anything the node already considers committed.**

Every payload index at or below the node's commit index carries an entry the
node already holds — by `AppliedCommitted` that entry is committed, and by
Leader Completeness the sending leader's log holds it too — so the consistency
scan finds no conflict there and the splice leaves the prefix untouched.
-/
theorem splice_preserves {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hr : Reachable members w) (h : SInv members w)
    {j src term l pi pt lc : Nat} {es : List Entry}
    (hpkt : (src, j, Msg.appendEntries term l pi pt es lc) ∈ w.sent)
    (hpi : pi ≤ LogStore.lastIndex (w.full j))
    (hchk : pi ≠ 0 → LogStore.termAt (w.full j) pi = some pt)
    (hct : (w.nodes j).currentTerm ≤ term) :
    ∀ k, k ≤ (w.nodes j).commitIndex →
      LogStore.get (appendFrom (w.full j) (pi + 1) es) k
        = LogStore.get (w.full j) k := by
  have hmsgL := msgFromLeaderLog_reachable hr
  obtain ⟨lgS, hS1, hS2, hS3, hS4⟩ := hmsgL src j term l pi pt es lc hpkt
  refine appendFrom_match_below es (w.full j) (pi + 1) (w.nodes j).commitIndex
    (by omega) ?_
  intro n e hn hle
  have hlen : n < es.length := by
    rcases Nat.lt_or_ge n es.length with hq | hq
    · exact hq
    · exact absurd hn (by rw [List.getElem?_eq_none hq]; simp)
  have hjl : pi + 1 + n ≤ LogStore.lastIndex (w.full j) := by
    have := h.bound j; omega
  obtain ⟨x, hx⟩ : ∃ x, LogStore.get (w.full j) (pi + 1 + n) = some x := by
    cases hq : LogStore.get (w.full j) (pi + 1 + n) with
    | none =>
        exfalso
        have := (LogStore.get_isSome_iff (w.full j) (pi + 1 + n)).mpr
          ⟨by rw [full_firstIndex hr j]; omega, by omega⟩
        rw [hq] at this; exact Bool.noConfusion this
    | some x => exact ⟨x, rfl⟩
  refine ⟨x, hx, ?_⟩
  have hSk : LogStore.get lgS (pi + 1 + n) = some e := hS2 n e hn
  obtain ⟨T', hcom, hT'⟩ := h.cov j (pi + 1 + n) x hle hx
  obtain ⟨L', c', lgc', Q', hc', hi', hg'⟩ := hcom
  obtain ⟨hcT', hL'⟩ := commit_ack_quorum hnd hr hc'
  have hxe : x = e := by
    rcases Nat.lt_or_ge T' term with hlt | hge
    · obtain ⟨hQ1, hQ2, hQ3, hQ4⟩ := commitQuorum_reachable hnd hr L' T' c' lgc' Q' hc'
      have hagree : AgreeUpTo lgS lgc' c' :=
        lc_aux hnd hr hL' hcT' ⟨Q', hQ1, hQ2, hQ3, hQ4⟩ term src term lgS hS1 hlt (Nat.le_refl _)
      have hq := hagree (pi + 1 + n) hi'
      rw [hSk, hg'] at hq
      exact (Option.some.inj hq).symm
    · have hTt : T' = term := by omega
      subst hTt
      have h1 := (llInv_reachable hnd hr).led L' T' lgc' hL'
      have h2 := (llInv_reachable hnd hr).led src T' lgS hS1
      have hLs : L' = src := led_unique hnd hr h1 h2
      subst hLs
      rcases (llInv_reachable hnd hr).chain L' T' lgc' lgS hL' hS1 with hp | hp
      · have hq := hp (pi + 1 + n)
          ((LogStore.get_isSome_iff lgc' (pi + 1 + n)).mp (by rw [hg']; rfl)).2
        rw [hg', hSk] at hq
        exact (Option.some.inj hq).symm
      · have hq := hp (pi + 1 + n)
          ((LogStore.get_isSome_iff lgS (pi + 1 + n)).mp (by rw [hSk]; rfl)).2
        rw [hg', hSk] at hq
        exact Option.some.inj hq
  rw [hxe]

/-- **The commitment invariants are preserved by every step.** -/
theorem sInv_step {members : List Nat} {w w' : World σ κ}
    (hnd : members.Nodup) (hr : Reachable members w)
    (h : SInv members w) (hs : Step members w w') : SInv members w' := by
  have hr' : Reachable members w' := Reachable.tail hr hs
  have hmsgL := msgFromLeaderLog_reachable hr
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev →
      (∀ src m', ev = Event.recv src m' → (src, j, m') ∈ w.sent) → SInv members w' := by
    intro j ev hw hdel
    subst hw
    -- a splice never disturbs anything the node already considers committed
    have keeps : ∀ (src term l pi pt lc : Nat) (es : List Entry),
        ev = Event.recv src (Msg.appendEntries term l pi pt es lc) →
        pi ≤ LogStore.lastIndex (w.full j) →
        (pi ≠ 0 → LogStore.termAt (w.full j) pi = some pt) →
        (w.nodes j).currentTerm ≤ term →
        ∀ k, k ≤ (w.nodes j).commitIndex →
          LogStore.get (appendFrom (w.full j) (pi + 1) es) k
            = LogStore.get (w.full j) k := by
      intro src term l pi pt lc es hev hpi hchk hct
      exact splice_preserves hnd hr h (hdel src _ hev) hpi hchk hct
    -- the commit index stays inside the log
    have hcb : CommitBound (w.act j ev) := by
      intro i
      have hbnd : ∀ q, (w.nodes q).commitIndex ≤ LogStore.lastIndex (w.nodes q).log := fun q => by
        rw [← full_lastIndex hr q]; exact h.bound q
      by_cases hij : i = j
      · subst hij
        rw [act_nodes_self, act_full_self]
        by_cases hae : ∃ (src term l pi pt : Nat) (es : List Entry) (lc : Nat),
            ev = Event.recv src (Msg.appendEntries term l pi pt es lc)
        · obtain ⟨src, term, l, pi, pt, es, lc, hev⟩ := hae
          subst hev
          rw [Protocol.step]
          by_cases hacc : Protocol.aeAccepts (w.nodes i) term pi pt = true
          · obtain ⟨hpi0, hchk0, hfw⟩ := aeAccepts_facts hacc
            rw [handleAppendEntries_commit, if_pos hacc, fullStep, if_pos hacc]
            have hpi : pi ≤ LogStore.lastIndex (w.full i) := by
              rw [full_lastIndex hr i]; exact hpi0
            have hchk : pi ≠ 0 → LogStore.termAt (w.full i) pi = some pt :=
              fun hz => full_termAt hr (hchk0 hz)
            have hct := aeAccepts_term hacc
            have hkeep := keeps src term l pi pt lc es rfl hpi hchk hct
            have hbr := appendFrom_bridge es (w.nodes i).log (w.full i) (pi + 1) hfw
              (full_firstIndex hr i) (full_lastIndex hr i) (fun k hk => full_get hr hk)
            rw [hbr.2.1]
            have hb1 : (w.nodes i).commitIndex
                ≤ LogStore.lastIndex (appendFrom (w.full i) (pi + 1) es) := by
              rcases Nat.eq_zero_or_pos (w.nodes i).commitIndex with h0 | h0
              · omega
              · obtain ⟨x, hx⟩ : ∃ x,
                    LogStore.get (w.full i) (w.nodes i).commitIndex = some x := by
                  cases hq : LogStore.get (w.full i) (w.nodes i).commitIndex with
                  | none =>
                      exfalso
                      have := (LogStore.get_isSome_iff (w.full i)
                        (w.nodes i).commitIndex).mpr
                        ⟨by rw [full_firstIndex hr i]; omega, h.bound i⟩
                      rw [hq] at this; exact Bool.noConfusion this
                  | some x => exact ⟨x, rfl⟩
                have hq := hkeep (w.nodes i).commitIndex (Nat.le_refl _)
                rw [hx] at hq
                exact ((LogStore.get_isSome_iff _ _).mp (by rw [hq]; rfl)).2
            omega
          · rw [handleAppendEntries_commit, if_neg hacc, fullStep, if_neg hacc]
            exact h.bound i
        · by_cases hadv : (w.nodes i).commitIndex < (Protocol.step (w.nodes i) ev).1.commitIndex
          · have hlead : (Protocol.step (w.nodes i) ev).1.role = Role.leader := by
              rcases step_commit_advance hadv with hl | ⟨src, term, l, pi, pt, es, lc, hev⟩
              · exact hl
              · exact absurd ⟨src, term, l, pi, pt, es, lc, hev⟩ hae
            have hct0 := commit_term_of_step hlead hadv
            have hct := full_termAt hr' (i := i)
              (k := (Protocol.step (w.nodes i) ev).1.commitIndex)
              (by rw [act_nodes_self]; exact hct0)
            rw [act_full_self] at hct
            unfold LogStore.termAt at hct
            cases hq : LogStore.get (fullStep (w.nodes i) (w.full i) ev)
                (Protocol.step (w.nodes i) ev).1.commitIndex with
            | none => rw [hq] at hct; simp at hct
            | some z => exact ((LogStore.get_isSome_iff _ _).mp (by rw [hq]; rfl)).2
          · have hlen : LogStore.lastIndex (w.full i)
                ≤ LogStore.lastIndex (fullStep (w.nodes i) (w.full i) ev) := by
              rcases full_step (w.nodes i) (w.full i) ev with hl | ⟨rid, cmd, _, _, hl⟩ |
                ⟨src, term, l, pi, pt, es, lc, hev, _⟩
              · rw [hl]; exact Nat.le_refl _
              · rw [hl, LogStore.lastIndex_append]; omega
              · exact absurd ⟨src, term, l, pi, pt, es, lc, hev⟩ hae
            have := h.bound i
            omega
      · rw [act_nodes_ne _ _ _ hij, act_full_ne _ _ _ hij]; exact h.bound i
    -- everything a node believes committed is committed
    have hcov : AppliedCommitted (w.act j ev) := by
      intro i k e hk hget
      by_cases hij : i = j
      · subst hij
        rw [act_nodes_self] at hk ⊢
        rw [act_full_self] at hget
        by_cases hae : ∃ (src term l pi pt : Nat) (es : List Entry) (lc : Nat),
            ev = Event.recv src (Msg.appendEntries term l pi pt es lc)
        · obtain ⟨src, term, l, pi, pt, es, lc, hev⟩ := hae
          subst hev
          rw [Protocol.step] at hk ⊢
          rw [fullStep] at hget
          by_cases hacc : Protocol.aeAccepts (w.nodes i) term pi pt = true
          · obtain ⟨hpi0, hchk0, hfw⟩ := aeAccepts_facts hacc
            have hpi : pi ≤ LogStore.lastIndex (w.full i) := by
              rw [full_lastIndex hr i]; exact hpi0
            have hchk : pi ≠ 0 → LogStore.termAt (w.full i) pi = some pt :=
              fun hz => full_termAt hr (hchk0 hz)
            have hct := aeAccepts_term hacc
            have hlg : (handleAppendEntries (w.nodes i) src term l pi pt es lc).1.log
                = appendFrom (w.nodes i).log (pi + 1) es := by
              rw [handleAppendEntries_accepts, if_pos hacc]
            have hci : (handleAppendEntries (w.nodes i) src term l pi pt es lc).1.commitIndex
                = max (w.nodes i).commitIndex
                  (min lc (LogStore.lastIndex (appendFrom (w.nodes i).log (pi + 1) es))) := by
              rw [handleAppendEntries_commit, if_pos hacc]
            rw [if_pos hacc] at hget
            rw [hci] at hk
            have hterm : (handleAppendEntries (w.nodes i) src term l pi pt es lc).1.currentTerm
                = term := by rw [handleAppendEntries_term_eq]; omega
            rw [hterm]
            rcases Nat.lt_or_ge (w.nodes i).commitIndex k with hbig | hsmall
            · -- newly learned: the leader's claim carries the evidence
              have hklc : k ≤ lc := by omega
              have hpkt := hdel src (Msg.appendEntries term l pi pt es lc) rfl
              obtain ⟨lgM, hM1, hM2, hS2, hS3, hS4, hM3⟩ :=
                h.msg src i term l pi pt es lc hpkt
              have hwfV : WellFormedLog w (w.full i) := wf_node hnd hr i
              have hpre' : pi ≤ LogStore.lastIndex lgM := prev_reach hr hwfV hchk hS3
              have hwfS : WellFormedLog w lgM := leaderLogWF_reachable hnd hr src term lgM hM1
              have hwfNew : WellFormedLog (w.act i
                  (Event.recv src (Msg.appendEntries term l pi pt es lc)))
                  (appendFrom (w.full i) (pi + 1) es) := by
                have h0 := wf_node hnd hr' i
                rw [act_full_self, fullStep, if_pos hacc] at h0
                exact h0
              have hsp := splice_agrees hnd hr' hwfV.mono hwfS.mono hpi hchk hS3 hS2 hwfNew
                k (by omega)
              rw [hsp] at hget
              obtain ⟨T', hcom, hT'⟩ := hM3 k e hklc hget
              exact ⟨T', committed_mono hcom, hT'⟩
            · -- already believed: the splice left it alone
              have hkeep := keeps src term l pi pt lc es rfl hpi hchk hct k hsmall
              rw [hkeep] at hget
              obtain ⟨T', hcom, hT'⟩ := h.cov i k e hsmall hget
              exact ⟨T', committed_mono hcom, by omega⟩
          · -- the payload was refused: nothing moved
            rw [if_neg hacc] at hget
            rw [handleAppendEntries_commit, if_neg hacc] at hk
            obtain ⟨T', hcom, hT'⟩ := h.cov i k e hk hget
            refine ⟨T', committed_mono hcom, ?_⟩
            have := handleAppendEntries_term (w.nodes i) src term l pi pt es lc
            omega
        · by_cases hadv : (w.nodes i).commitIndex < (Protocol.step (w.nodes i) ev).1.commitIndex
          · have hlead : (Protocol.step (w.nodes i) ev).1.role = Role.leader := by
              rcases step_commit_advance hadv with hl | ⟨src, term, l, pi, pt, es, lc, hev⟩
              · exact hl
              · exact absurd ⟨src, term, l, pi, pt, es, lc, hev⟩ hae
            refine ⟨(Protocol.step (w.nodes i) ev).1.currentTerm, ?_, Nat.le_refl _⟩
            exact ⟨i, (Protocol.step (w.nodes i) ev).1.commitIndex,
              fullStep (w.nodes i) (w.full i) ev,
              replicatedOn (Protocol.step (w.nodes i) ev).1
                (Protocol.step (w.nodes i) ev).1.commitIndex,
              List.mem_append_right _ (mem_commitOf_self hlead hadv), hk, hget⟩
          · have hk' : k ≤ (w.nodes i).commitIndex := by omega
            have hunch : LogStore.get (fullStep (w.nodes i) (w.full i) ev) k
                = LogStore.get (w.full i) k := by
              rcases full_step (w.nodes i) (w.full i) ev with hl | ⟨rid, cmd, _, _, hl⟩ |
                ⟨src, term, l, pi, pt, es, lc, hev, _⟩
              · rw [hl]
              · rw [hl, LogStore.get_append, if_neg (by have := h.bound i; omega)]
              · exact absurd ⟨src, term, l, pi, pt, es, lc, hev⟩ hae
            rw [hunch] at hget
            obtain ⟨T', hcom, hT'⟩ := h.cov i k e hk' hget
            refine ⟨T', committed_mono hcom, ?_⟩
            have := step_term_mono (w.nodes i) ev
            omega
      · rw [act_nodes_ne _ _ _ hij] at hk ⊢
        rw [act_full_ne _ _ _ hij] at hget
        obtain ⟨T', hcom, hT'⟩ := h.cov i k e hk hget
        exact ⟨T', committed_mono hcom, hT'⟩
    -- what a leader advertises is what it believes
    refine ⟨hcb, ?_, hcov⟩
    intro src dst t l pi pt es lc hp
    rw [act_sent] at hp
    rcases List.mem_append.mp hp with hp' | hp'
    · obtain ⟨lgM, h1, h2, hp2, hp3, hp4, h3⟩ := h.msg src dst t l pi pt es lc hp'
      exact ⟨lgM, leaderLog_mono h1, h2, hp2, hp3, hp4,
        fun k e hk hget => by
          obtain ⟨T', hcom, hT'⟩ := h3 k e hk hget
          exact ⟨T', committed_mono hcom, hT'⟩⟩
    · rcases mem_sendsOf hp' with ⟨to, m, heq, hact⟩
      have hsj : src = j := congrArg (fun q => q.1) heq
      have hm : m = Msg.appendEntries t l pi pt es lc := by
        have := congrArg (fun q => q.2.2) heq; simpa using this.symm
      subst hm; subst hsj
      obtain ⟨hlead, hterm⟩ := step_appendEntries_leader hact
      obtain ⟨p0, hp0⟩ := step_appendEntries_payload hact
      simp only [appendEntriesTo] at hp0
      obtain ⟨_, _, hpi, hpt, hes, hlc⟩ := Msg.appendEntries.inj hp0
      have hni : max (LogStore.sendFloor (Protocol.step (w.nodes src) ev).1.log)
          (PeerMap.get (Protocol.step (w.nodes src) ev).1.nextIndex p0
          (LogStore.lastIndex (Protocol.step (w.nodes src) ev).1.log + 1)) = pi + 1 := by
        rw [hpi]
        have := Nat.le_max_left (LogStore.sendFloor (Protocol.step (w.nodes src) ev).1.log)
          (PeerMap.get (Protocol.step (w.nodes src) ev).1.nextIndex p0
            (LogStore.lastIndex (Protocol.step (w.nodes src) ev).1.log + 1))
        have := LogStore.one_le_sendFloor (Protocol.step (w.nodes src) ev).1.log
        omega
      have hfloor : LogStore.sendFloor (Protocol.step (w.nodes src) ev).1.log ≤ pi + 1 := by
        rw [← hni]; exact Nat.le_max_left _ _
      have hfl : LogStore.firstIndex (Protocol.step (w.nodes src) ev).1.log ≤
          max (LogStore.sendFloor (Protocol.step (w.nodes src) ev).1.log)
            (PeerMap.get (Protocol.step (w.nodes src) ev).1.nextIndex p0
              (LogStore.lastIndex (Protocol.step (w.nodes src) ev).1.log + 1)) :=
        Nat.le_trans (LogStore.firstIndex_le_sendFloor _) (Nat.le_max_left _ _)
      refine ⟨fullStep (w.nodes src) (w.full src) ev, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [act_leaderLogs]
        exact List.mem_append_right _ (hterm ▸ leaderLogOf_self hlead)
      · have hb := hcb src
        rw [act_nodes_self, act_full_self] at hb
        rw [hlc]; exact hb
      · intro n e hn
        rw [hes] at hn
        have hq := appendEntriesTo_entries (s := (Protocol.step (w.nodes src) ev).1) (p := p0) hn
        rw [hni] at hq
        have := full_get_of hr' (i := src) (by rw [act_nodes_self]; exact hq)
        rwa [act_full_self] at this
      · have hb := full_termAt_getD hr' (i := src) (k := pi) ?_
        · rw [act_nodes_self, act_full_self] at hb
          rw [hb, hpt, ← hpi]
        · rw [act_nodes_self]
          rcases Nat.eq_zero_or_pos pi with hz | hz
          · exact Or.inl hz
          · exact Or.inr (Nat.le_of_lt_succ
              (LogStore.first_lt_of_sendFloor hfloor (by omega)))
      · have hlen := congrArg List.length
          (model_sliceFrom (Protocol.step (w.nodes src) ev).1.log _ hfl)
        simp only [List.length_map, List.length_drop] at hlen
        have hli := full_lastIndex hr' (i := src)
        rw [act_nodes_self, act_full_self] at hli
        rw [hes, hlen, hni, hli]
        simp [LogStore.lastIndex, model_size]
      · intro k e hk hget
        have hcv := hcov src k e (by rw [act_nodes_self]; omega)
          (by rw [act_full_self]; exact hget)
        obtain ⟨T', hcom, hT'⟩ := hcv
        refine ⟨T', hcom, ?_⟩
        rw [act_nodes_self] at hT'
        omega
  cases hs with
  | deliver s d m0 hd hmem =>
      refine key d _ rfl ?_
      intro src' m' heq
      have h1 : s = src' := (Event.recv.inj heq).1
      have h2 : m0 = m' := (Event.recv.inj heq).2
      subst h2; subst h1; exact hmem
  | electionTimeout k hk => exact key k _ rfl (fun _ _ hq => Event.noConfusion hq)
  | heartbeat k hk => exact key k _ rfl (fun _ _ hq => Event.noConfusion hq)
  | client k rid cmd hk => exact key k _ rfl (fun _ _ hq => Event.noConfusion hq)
  | crash k hk =>
      -- a restart zeroes the volatile indices, so its own claims become vacuous
      refine ⟨?_, ?_, ?_⟩
      · intro i
        by_cases hik : i = k
        · subst hik; rw [crash_nodes_self, restart_commitIndex]; omega
        · rw [crash_nodes_ne _ _ hik]; exact h.bound i
      · intro src dst t l pi pt es lc hp
        rw [crash_sent] at hp
        obtain ⟨lgM, h1, h2, hp2, hp3, hp4, h3⟩ := h.msg src dst t l pi pt es lc hp
        refine ⟨lgM, by rw [crash_leaderLogs]; exact h1, h2, hp2, hp3, hp4, ?_⟩
        intro k' e hk' hget
        obtain ⟨T', hcom, hT'⟩ := h3 k' e hk' hget
        exact ⟨T', committed_crash_mono hcom, hT'⟩
      · intro i k' e hk' hget
        rw [crash_full] at hget
        by_cases hik : i = k
        · exfalso
          subst hik
          rw [crash_nodes_self, restart_commitIndex] at hk'
          have hz : k' = 0 := by omega
          rw [hz] at hget
          simp at hget
        · rw [crash_nodes_ne _ _ hik] at hk' ⊢
          obtain ⟨T', hcom, hT'⟩ := h.cov i k' e hk' hget
          exact ⟨T', committed_crash_mono hcom, hT'⟩

theorem sInv_reachable {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) : SInv members w := by
  induction h with
  | init => exact sInv_init members
  | tail hr hs ih => exact sInv_step hnd hr ih hs


/--
**A step never disturbs a node's log at or below what it has already applied.**

The three ways a log can change: it does not, it gains one entry at the top, or
it is spliced — and a splice preserves everything at or below the commit index,
which is at least `lastApplied`.
-/
theorem step_log_below_applied {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hr : Reachable members w) {j : Nat} {ev : Event}
    (hdel : ∀ src m', ev = Event.recv src m' → (src, j, m') ∈ w.sent) :
    ∀ k, k ≤ (w.nodes j).lastApplied →
      LogStore.get (fullStep (w.nodes j) (w.full j) ev) k = LogStore.get (w.full j) k := by
  have hsi := sInv_reachable hnd hr
  have hab := appliedBound_reachable hr
  intro k hk
  rcases full_step (w.nodes j) (w.full j) ev with hl | ⟨rid, cmd, _, _, hl⟩ |
    ⟨src, term, l, pi, pt, es, lc, hev, ha, hl⟩
  · rw [hl]
  · rw [hl, LogStore.get_append, if_neg (by have := hab j; have := hsi.bound j; omega)]
  · rw [hl]
    obtain ⟨hpi0, hchk0, hfw⟩ := aeAccepts_facts ha
    have hpi : pi ≤ LogStore.lastIndex (w.full j) := by
      rw [full_lastIndex hr j]; exact hpi0
    have hchk : pi ≠ 0 → LogStore.termAt (w.full j) pi = some pt :=
      fun hz => full_termAt hr (hchk0 hz)
    exact splice_preserves hnd hr hsi (hdel src _ hev) hpi hchk (aeAccepts_term ha) k
      (Nat.le_trans hk (hab j))

/-- **State Machine Safety.** Two replicas never apply different entries at one index. -/
theorem stateMachineSafety {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) : Protocol.StateMachineSafety w := by
  intro i j idx e₁ e₂ hi hj hg₁ hg₂
  have hab := appliedBound_reachable hrch
  have hs := sInv_reachable hnd hrch
  obtain ⟨T₁, hc₁, _⟩ := hs.cov i idx e₁ (Nat.le_trans hi (hab i)) hg₁
  obtain ⟨T₂, hc₂, _⟩ := hs.cov j idx e₂ (Nat.le_trans hj (hab j)) hg₂
  exact committed_unique hnd hrch hc₁ hc₂

end RaftKV.Proof
