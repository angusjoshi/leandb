import RaftKV.Proof.AppendProv

/-!
# The ghost logical log, and the one bridge to what a node holds

`World.full` is each node's log **as it would be had nothing ever been
compacted**. Every safety invariant in this development is a claim about what
logs contain, and compaction takes a prefix away, so those claims would all have
to be weakened with a window condition — and some of them become outright false
that way, because two *recorded* logs can have discarded different amounts and
then simply cannot be compared at a low index.

Stating the invariants over `full` avoids all of that. What is left is this
file: the logical log takes the same operation the real one does, and the two
agree everywhere the real one can still be asked.

That is the modular payoff. Adding compaction costs one invariant here, not a
window condition threaded through every theorem downstream.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [LawfulLogStore σ] [KVStore κ]

/-- **How a step can change the logical log** — the mirror of `step_log`. -/
theorem full_step (s : NodeState σ κ) (fl : σ) (ev : Event) :
    fullStep s fl ev = fl
      ∨ (∃ rid cmd, ev = Event.clientReq rid cmd ∧ s.role = Role.leader
          ∧ fullStep s fl ev
              = LogStore.append fl { term := s.currentTerm, cmd := cmd, reqId := rid })
      ∨ (∃ src term l pi pt es lc,
          ev = Event.recv src (Msg.appendEntries term l pi pt es lc)
          ∧ Protocol.aeAccepts s term pi pt = true
          ∧ fullStep s fl ev = appendFrom fl (pi + 1) es) := by
  cases ev with
  | clientReq rid cmd =>
      by_cases hl : s.role = Role.leader
      · exact Or.inr (Or.inl ⟨rid, cmd, rfl, hl, by rw [fullStep, if_pos hl]⟩)
      · exact Or.inl (by rw [fullStep, if_neg hl])
  | recv src m =>
      cases m with
      | appendEntries term l pi pt es lc =>
          by_cases ha : Protocol.aeAccepts s term pi pt = true
          · exact Or.inr (Or.inr ⟨src, term, l, pi, pt, es, lc, rfl, ha,
              by rw [fullStep, if_pos ha]⟩)
          · exact Or.inl (by rw [fullStep, if_neg ha])
      | requestVote _ _ _ _ => exact Or.inl rfl
      | requestVoteResp _ _ => exact Or.inl rfl
      | appendEntriesResp _ _ _ => exact Or.inl rfl
  | electionTimeout => exact Or.inl rfl
  | heartbeatTimeout => exact Or.inl rfl

/-! ## Splicing two logs that agree above a window -/

/--
The splice makes the same decisions on two logs that agree wherever the shorter
window can be asked, and the results still agree there.

This is the whole content of the bridge: `appendFrom` reads the log only at
indices from `startIdx` upwards, and `startIdx` is inside the window because the
consistency check put it there.
-/
theorem appendFrom_bridge :
    ∀ (es : List Entry) (lg fl : σ) (startIdx : Nat),
      LogStore.firstIndex lg ≤ startIdx →
      LogStore.firstIndex fl = 1 →
      LogStore.lastIndex fl = LogStore.lastIndex lg →
      (∀ k, LogStore.firstIndex lg ≤ k → LogStore.get lg k = LogStore.get fl k) →
      LogStore.firstIndex (appendFrom fl startIdx es) = 1
        ∧ LogStore.lastIndex (appendFrom fl startIdx es)
            = LogStore.lastIndex (appendFrom lg startIdx es)
        ∧ ∀ k, LogStore.firstIndex (appendFrom lg startIdx es) ≤ k →
            LogStore.get (appendFrom lg startIdx es) k
              = LogStore.get (appendFrom fl startIdx es) k := by
  intro es
  induction es with
  | nil =>
      intro lg fl startIdx _ hf1 hlast hag
      exact ⟨hf1, hlast, hag⟩
  | cons e es ih =>
    intro lg fl startIdx hfs hf1 hlast hag
    have hposl := LawfulLogStore.first_pos lg
    have hsame : LogStore.get fl startIdx = LogStore.get lg startIdx := (hag startIdx hfs).symm
    rw [appendFrom, appendFrom, hsame]
    cases hg : LogStore.get lg startIdx with
    | some existing =>
        dsimp only
        by_cases hterm : existing.term == e.term
        · rw [if_pos hterm, if_pos hterm]
          exact ih lg fl (startIdx + 1) (by omega) hf1 hlast hag
        · rw [if_neg hterm, if_neg hterm]
          have hle : startIdx ≤ LogStore.lastIndex lg := LogStore.le_lastIndex_of_get hg
          have hftl : LogStore.firstIndex (LogStore.truncFrom lg startIdx)
              = LogStore.firstIndex lg := by
            rw [LawfulLogStore.first_truncFrom]; omega
          have hftf : LogStore.firstIndex (LogStore.truncFrom fl startIdx) = 1 := by
            rw [LawfulLogStore.first_truncFrom, hf1]; omega
          refine ih _ _ (startIdx + 1) (by rw [LawfulLogStore.first_append, hftl]; omega)
            (by rw [LawfulLogStore.first_append, hftf]) ?_ ?_
          · rw [LogStore.lastIndex_append, LogStore.lastIndex_append,
              LogStore.lastIndex_truncFrom_of_le _ _ (by omega),
              LogStore.lastIndex_truncFrom_of_le _ _ hle]
          · intro k hk
            rw [LawfulLogStore.first_append, hftl] at hk
            rw [LogStore.get_append, LogStore.get_append,
              LogStore.lastIndex_truncFrom_of_le _ _ hle,
              LogStore.lastIndex_truncFrom_of_le _ _ (by omega)]
            split
            · rfl
            · rw [LogStore.get_truncFrom, LogStore.get_truncFrom]
              split
              · exact hag k hk
              · rfl
    | none =>
        dsimp only
        have hnl : LogStore.lastIndex lg < startIdx := by
          rcases Nat.lt_or_ge (LogStore.lastIndex lg) startIdx with hc | hc
          · exact hc
          · exact absurd ((LogStore.get_isSome_iff lg startIdx).mpr ⟨hfs, hc⟩)
              (by rw [hg]; simp)
        refine ih _ _ (startIdx + 1) (by rw [LawfulLogStore.first_append]; omega)
          (by rw [LawfulLogStore.first_append, hf1]) ?_ ?_
        · rw [LogStore.lastIndex_append, LogStore.lastIndex_append, hlast]
        · intro k hk
          rw [LawfulLogStore.first_append] at hk
          rw [LogStore.get_append, LogStore.get_append, hlast]
          split
          · rfl
          · exact hag k hk

/-! ## The bridge invariant -/

/-- The logical log never discards, reaches exactly as far, and agrees in the window. -/
structure FullBridge (w : World σ κ) : Prop where
  /-- The logical log has discarded nothing. -/
  first : ∀ i, LogStore.firstIndex (w.full i) = 1
  /-- It reaches exactly as far as the real one. -/
  last : ∀ i, LogStore.lastIndex (w.full i) = LogStore.lastIndex (w.nodes i).log
  /-- And agrees wherever the real one can still be asked. -/
  agree : ∀ i k, LogStore.firstIndex (w.nodes i).log ≤ k →
    LogStore.get (w.nodes i).log k = LogStore.get (w.full i) k
  /--
  The window is sane: either nothing has been discarded, or the window is
  non-empty. A node never compacts past its own end, and the consistency check
  never lets a splice truncate into the discarded region.
  -/
  window : ∀ i, LogStore.firstIndex (w.nodes i).log = 1
    ∨ LogStore.firstIndex (w.nodes i).log ≤ LogStore.lastIndex (w.nodes i).log

theorem fullBridge_init (members : List Nat) :
    FullBridge (σ := σ) (κ := κ) (World.init members) where
  first := fun _ => LawfulLogStore.first_empty
  last := fun _ => rfl
  agree := fun _ _ _ => rfl
  window := fun _ => Or.inl LawfulLogStore.first_empty

theorem fullBridge_step {members : List Nat} {w w' : World σ κ}
    (h : FullBridge w) (hs : Step members w w') : FullBridge w' := by
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev → FullBridge w' := by
    intro j ev hw
    subst hw
    have main : LogStore.firstIndex (fullStep (w.nodes j) (w.full j) ev) = 1
        ∧ LogStore.lastIndex (fullStep (w.nodes j) (w.full j) ev)
            = LogStore.lastIndex (Protocol.step (w.nodes j) ev).1.log
        ∧ ∀ k, LogStore.firstIndex (Protocol.step (w.nodes j) ev).1.log ≤ k →
            LogStore.get (Protocol.step (w.nodes j) ev).1.log k
              = LogStore.get (fullStep (w.nodes j) (w.full j) ev) k := by
      have hunchanged : ∀ (ev' : Event),
          (Protocol.step (w.nodes j) ev').1.log = (w.nodes j).log →
          fullStep (w.nodes j) (w.full j) ev' = w.full j →
          LogStore.firstIndex (fullStep (w.nodes j) (w.full j) ev') = 1
            ∧ LogStore.lastIndex (fullStep (w.nodes j) (w.full j) ev')
                = LogStore.lastIndex (Protocol.step (w.nodes j) ev').1.log
            ∧ ∀ k, LogStore.firstIndex (Protocol.step (w.nodes j) ev').1.log ≤ k →
                LogStore.get (Protocol.step (w.nodes j) ev').1.log k
                  = LogStore.get (fullStep (w.nodes j) (w.full j) ev') k := by
        intro ev' hn hf
        rw [hn, hf]
        exact ⟨h.first j, h.last j, h.agree j⟩
      cases ev with
      | electionTimeout =>
          refine hunchanged _ ?_ rfl
          rcases step_log (w.nodes j) Event.electionTimeout with hn | ⟨_, _, hev, _⟩ |
            ⟨_, _, _, _, _, _, _, hev, _⟩
          · exact hn
          · exact absurd hev (by simp)
          · exact absurd hev (by simp)
      | heartbeatTimeout =>
          refine hunchanged _ ?_ rfl
          rcases step_log (w.nodes j) Event.heartbeatTimeout with hn | ⟨_, _, hev, _⟩ |
            ⟨_, _, _, _, _, _, _, hev, _⟩
          · exact hn
          · exact absurd hev (by simp)
          · exact absurd hev (by simp)
      | clientReq rid cmd =>
          by_cases hlead : (w.nodes j).role = Role.leader
          · rw [fullStep, if_pos hlead, Protocol.step, handleClientReq_log hlead]
            refine ⟨by rw [LawfulLogStore.first_append]; exact h.first j, ?_, ?_⟩
            · rw [LogStore.lastIndex_append, LogStore.lastIndex_append, h.last j]
            · intro k hk
              rw [LawfulLogStore.first_append] at hk
              rw [LogStore.get_append, LogStore.get_append, h.last j]
              split
              · rfl
              · exact h.agree j k hk
          · refine hunchanged _ ?_ (by rw [fullStep, if_neg hlead])
            rw [Protocol.step, handleClientReq, if_pos (by simp [hlead])]
      | recv src m =>
          cases m with
          | requestVote a b c d =>
              refine hunchanged _ ?_ rfl
              rcases step_log (w.nodes j) (Event.recv src (Msg.requestVote a b c d))
                with hn | ⟨_, _, hev, _⟩ | ⟨_, _, _, _, _, _, _, hev, _⟩
              · exact hn
              · exact absurd hev (by simp)
              · exact absurd hev (by simp)
          | requestVoteResp a b =>
              refine hunchanged _ ?_ rfl
              rcases step_log (w.nodes j) (Event.recv src (Msg.requestVoteResp a b))
                with hn | ⟨_, _, hev, _⟩ | ⟨_, _, _, _, _, _, _, hev, _⟩
              · exact hn
              · exact absurd hev (by simp)
              · exact absurd hev (by simp)
          | appendEntriesResp a b c =>
              refine hunchanged _ ?_ rfl
              rcases step_log (w.nodes j) (Event.recv src (Msg.appendEntriesResp a b c))
                with hn | ⟨_, _, hev, _⟩ | ⟨_, _, _, _, _, _, _, hev, _⟩
              · exact hn
              · exact absurd hev (by simp)
              · exact absurd hev (by simp)
          | appendEntries term l pi pt es lc =>
              by_cases ha : Protocol.aeAccepts (w.nodes j) term pi pt = true
              · obtain ⟨_, _, hfw⟩ := aeAccepts_facts ha
                rw [fullStep, if_pos ha, Protocol.step, handleAppendEntries_accepts,
                  if_pos ha]
                exact appendFrom_bridge es (w.nodes j).log (w.full j) (pi + 1) hfw
                  (h.first j) (h.last j) (h.agree j)
              · refine hunchanged _ ?_ (by rw [fullStep, if_neg ha])
                rw [Protocol.step, handleAppendEntries_accepts, if_neg ha]
    refine ⟨fun i => ?_, fun i => ?_, fun i k hk => ?_, fun i => ?_⟩
    · by_cases hij : i = j
      · subst hij; rw [act_full_self]; exact main.1
      · rw [act_full_ne _ _ _ hij]; exact h.first i
    · by_cases hij : i = j
      · subst hij; rw [act_full_self, act_nodes_self]; exact main.2.1
      · rw [act_full_ne _ _ _ hij, act_nodes_ne _ _ _ hij]; exact h.last i
    · by_cases hij : i = j
      · subst hij
        rw [act_nodes_self] at hk
        rw [act_full_self, act_nodes_self]
        exact main.2.2 k hk
      · rw [act_nodes_ne _ _ _ hij] at hk
        rw [act_full_ne _ _ _ hij, act_nodes_ne _ _ _ hij]
        exact h.agree i k hk
    · by_cases hij : i = j
      · subst hij
        rw [act_nodes_self]
        rcases step_log (w.nodes i) ev with hn | ⟨rid, cmd, _, hn⟩ |
          ⟨src, term, l, pi, pt, es, lc, hev, hn, hpi, hchk, hfw, _, _⟩
        · rw [hn]; exact h.window i
        · rw [hn, LawfulLogStore.first_append, LogStore.lastIndex_append]
          rcases h.window i with hc | hc
          · exact Or.inl hc
          · exact Or.inr (by omega)
        · rw [hn, appendFrom_firstIndex es (w.nodes i).log (pi + 1) hfw]
          have hge := appendFrom_lastIndex_ge es (w.nodes i).log (pi + 1) (by omega)
          rcases Classical.em (LogStore.firstIndex (w.nodes i).log = 1) with hc | hc
          · exact Or.inl hc
          · refine Or.inr ?_
            have hpos : pi ≠ 0 := by
              intro hz
              subst hz
              exact hc (Nat.le_antisymm hfw (LawfulLogStore.first_pos _))
            have := LogStore.firstIndex_le_of_termAt (hchk hpos)
            omega
      · rw [act_nodes_ne _ _ _ hij]; exact h.window i
  cases hs with
  | deliver s d m hd hmem => exact key d _ rfl
  | electionTimeout k hk => exact key k _ rfl
  | heartbeat k hk => exact key k _ rfl
  | client k rid cmd hk => exact key k _ rfl
  | crash k hk =>
      refine ⟨fun i => ?_, fun i => ?_, fun i k' hk' => ?_, fun i => ?_⟩
      · rw [crash_full]; exact h.first i
      · rw [crash_full]
        by_cases hij : i = k
        · subst hij; rw [crash_nodes_self, restart_log]; exact h.last i
        · rw [crash_nodes_ne _ _ hij]; exact h.last i
      · rw [crash_full]
        by_cases hij : i = k
        · subst hij; rw [crash_nodes_self, restart_log] at hk' ⊢; exact h.agree i k' hk'
        · rw [crash_nodes_ne _ _ hij] at hk' ⊢; exact h.agree i k' hk'
      · by_cases hij : i = k
        · subst hij; rw [crash_nodes_self, restart_log]; exact h.window i
        · rw [crash_nodes_ne _ _ hij]; exact h.window i

/-- **The bridge holds in every reachable world.** -/
theorem fullBridge_reachable {members : List Nat} {w : World σ κ}
    (h : Reachable members w) : FullBridge w := by
  induction h with
  | init => exact fullBridge_init members
  | tail _ hs ih => exact fullBridge_step ih hs

/-- The logical log is the real one wherever the real one can still be asked. -/
theorem full_get {members : List Nat} {w : World σ κ} (h : Reachable members w)
    {i k : Nat} (hk : LogStore.firstIndex (w.nodes i).log ≤ k) :
    LogStore.get (w.nodes i).log k = LogStore.get (w.full i) k :=
  (fullBridge_reachable h).agree i k hk

/-- An entry the real log holds, the logical log holds too. -/
theorem full_get_of {members : List Nat} {w : World σ κ} (h : Reachable members w)
    {i k : Nat} {e : Entry} (hg : LogStore.get (w.nodes i).log k = some e) :
    LogStore.get (w.full i) k = some e := by
  rw [← full_get h (LogStore.firstIndex_le_of_get hg)]; exact hg

/-- A term the real log reports, the logical log reports too. -/
theorem full_termAt {members : List Nat} {w : World σ κ} (h : Reachable members w)
    {i k t : Nat} (hg : LogStore.termAt (w.nodes i).log k = some t) :
    LogStore.termAt (w.full i) k = some t := by
  unfold LogStore.termAt at hg ⊢
  cases hq : LogStore.get (w.nodes i).log k with
  | none => rw [hq] at hg; exact absurd hg (by simp)
  | some e => rw [← full_get h (LogStore.firstIndex_le_of_get hq), hq]; rw [hq] at hg; exact hg

/-- The last term is the same in both logs. -/
theorem full_lastTerm {members : List Nat} {w : World σ κ} (h : Reachable members w) (i : Nat) :
    LogStore.lastTerm (w.full i) = LogStore.lastTerm (w.nodes i).log := by
  have hb := fullBridge_reachable h
  unfold LogStore.lastTerm LogStore.termAt LogStore.lastIndex
  have hlast : LogStore.size (w.full i) = LogStore.size (w.nodes i).log := hb.last i
  rw [← hlast]
  rcases Nat.eq_zero_or_pos (LogStore.size (w.full i)) with hz | hz
  · rw [hz]
    have h0 : LogStore.get (w.nodes i).log 0 = none := LogStore.get_zero _
    rw [h0]
    have h1 : LogStore.get (w.full i) 0 = none := LogStore.get_zero _
    rw [h1]
  · have hfi : LogStore.firstIndex (w.nodes i).log ≤ LogStore.size (w.full i) := by
      rcases hb.window i with hc | hc
      · rw [hc]; omega
      · simp only [LogStore.lastIndex] at hc; omega
    rw [hb.agree i _ hfi]

/-- The two logs reach exactly as far as each other. -/
theorem full_lastIndex {members : List Nat} {w : World σ κ} (h : Reachable members w) (i : Nat) :
    LogStore.lastIndex (w.full i) = LogStore.lastIndex (w.nodes i).log :=
  (fullBridge_reachable h).last i

/-- The logical log has no holes: an entry at `idx` implies entries at every index below. -/
theorem full_isSome_below {members : List Nat} {w : World σ κ} (h : Reachable members w)
    {i idx m : Nat} {e : Entry} (hg : LogStore.get (w.full i) idx = some e)
    (h1 : 1 ≤ m) (hm : m ≤ idx) : (LogStore.get (w.full i) m).isSome := by
  have hidx := (LogStore.get_isSome_iff (w.full i) idx).mp (by rw [hg]; rfl)
  refine (LogStore.get_isSome_iff (w.full i) m).mpr ⟨?_, by omega⟩
  rw [(fullBridge_reachable h).first i]; omega

/-- The logical log has discarded nothing. -/
theorem full_firstIndex {members : List Nat} {w : World σ κ} (h : Reachable members w) (i : Nat) :
    LogStore.firstIndex (w.full i) = 1 :=
  (fullBridge_reachable h).first i

end RaftKV.Proof
