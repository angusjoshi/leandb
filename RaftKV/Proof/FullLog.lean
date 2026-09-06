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

/--
**No step moves the live window.**

Every handler either leaves the log alone, appends, or splices at an index the
consistency check placed inside the window — and none of those discards a
prefix. Compaction is the one operation that does.
-/
theorem step_firstIndex (s : NodeState σ κ) (ev : Event) (hev : ev.isSnapRecv = false) :
    LogStore.firstIndex (Protocol.step s ev).1.log = LogStore.firstIndex s.log := by
  rcases step_log s ev with hl | ⟨rid, cmd, _, hl⟩ |
    ⟨src, term, l, pi, pt, es, lc, _, hl, _, _, hfw, _, _⟩ |
    ⟨src, term, lid, lastIdx, anchor, pairs, hev', _⟩
  · rw [hl]
  · rw [hl, LawfulLogStore.first_append]
  · rw [hl, appendFrom_firstIndex es s.log (pi + 1) hfw]
  · exact absurd hev (by rw [hev']; simp [Event.isSnapRecv])

/-- **How a step can change the logical log** — the mirror of `step_log`. -/
theorem full_step (s : NodeState σ κ) (fl : σ) (ev : Event) :
    nodeFullStep s fl ev = fl
      ∨ (∃ rid cmd, ev = Event.clientReq rid cmd ∧ s.role = Role.leader
          ∧ nodeFullStep s fl ev
              = LogStore.append fl { term := s.currentTerm, cmd := cmd, reqId := rid })
      ∨ (∃ src term l pi pt es lc,
          ev = Event.recv src (Msg.appendEntries term l pi pt es lc)
          ∧ Protocol.aeAccepts s term pi pt = true
          ∧ nodeFullStep s fl ev = appendFrom fl (pi + 1) es) := by
  cases ev with
  | clientReq rid cmd =>
      by_cases hl : s.role = Role.leader
      · exact Or.inr (Or.inl ⟨rid, cmd, rfl, hl, by rw [nodeFullStep, if_pos hl]⟩)
      · exact Or.inl (by rw [nodeFullStep, if_neg hl])
  | recv src m =>
      cases m with
      | appendEntries term l pi pt es lc =>
          by_cases ha : Protocol.aeAccepts s term pi pt = true
          · exact Or.inr (Or.inr ⟨src, term, l, pi, pt, es, lc, rfl, ha,
              by rw [nodeFullStep, if_pos ha]⟩)
          · exact Or.inl (by rw [nodeFullStep, if_neg ha])
      | requestVote _ _ _ _ => exact Or.inl rfl
      | requestVoteResp _ _ => exact Or.inl rfl
      | appendEntriesResp _ _ _ => exact Or.inl rfl
      | installSnapshot _ _ _ _ _ => exact Or.inl rfl
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

/-- A leader's logical log only ever grows, exactly as its real one does. -/
theorem step_full_of_leader (s : NodeState σ κ) (fl : σ) (ev : Event)
    (hlold : s.role = Role.leader) (hl : (Protocol.step s ev).1.role = Role.leader) :
    nodeFullStep s fl ev = fl ∨ ∃ e, nodeFullStep s fl ev = LogStore.append fl e := by
  rcases full_step s fl ev with h | ⟨rid, cmd, _, _, h⟩ | ⟨src, term, l, pi, pt, es, lc, hev, ha, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨_, h⟩
  · exfalso
    subst hev
    have hct := aeAccepts_term ha
    rw [Protocol.step, handleAppendEntries, if_neg (by omega)] at hl
    dsimp only at hl
    split at hl <;> simp at hl

/-- The guards the installer checks, unpacked. -/
theorem snapInstalls_facts {s : NodeState σ κ} {term lastIdx : Nat} {anchor : Entry}
    (h : Protocol.snapInstalls s term lastIdx anchor = true) :
    ¬ (term < s.currentTerm) ∧ 2 ≤ lastIdx ∧ s.commitIndex < lastIdx := by
  rw [Protocol.snapInstalls] at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not] at h
  exact ⟨by simpa using h.1.1.1, h.1.2, h.2⟩

/--
**How a step can change the logical log, in the world.**

The first three cases are `full_step`'s. The fourth is the snapshot: the
receiver's logical log is replaced wholesale, and what it becomes is a fact about
the *sender*, so it is left to `snapInstall_facts` to say.
-/
theorem world_full_step (w : World σ κ) (i : Nat) (ev : Event) :
    fullStep w i ev = w.full i
      ∨ (∃ rid cmd, ev = Event.clientReq rid cmd ∧ (w.nodes i).role = Role.leader
          ∧ fullStep w i ev = LogStore.append (w.full i)
              { term := (w.nodes i).currentTerm, cmd := cmd, reqId := rid })
      ∨ (∃ src term l pi pt es lc,
          ev = Event.recv src (Msg.appendEntries term l pi pt es lc)
          ∧ Protocol.aeAccepts (w.nodes i) term pi pt = true
          ∧ fullStep w i ev = appendFrom (w.full i) (pi + 1) es)
      ∨ (∃ (src term lid lastIdx : Nat) (anchor : Entry) (pairs : List (String × String)),
          ev = Event.recv src (Msg.installSnapshot term lid lastIdx anchor pairs)
          ∧ Protocol.snapInstalls (w.nodes i) term lastIdx anchor = true
          ∧ (w.nodes i).currentTerm ≤ term) := by
  by_cases hsr : ev.isSnapRecv = false
  · rw [fullStep_node w i ev hsr]
    rcases full_step (w.nodes i) (w.full i) ev with hl | ⟨rid, cmd, h1, h2, h3⟩ |
      ⟨src, term, l, pi, pt, es, lc, h1, h2, h3⟩
    · exact Or.inl hl
    · exact Or.inr (Or.inl ⟨rid, cmd, h1, h2, h3⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨src, term, l, pi, pt, es, lc, h1, h2, h3⟩))
  · have hsr' : ev.isSnapRecv = true := by simpa using hsr
    cases ev with
    | clientReq _ _ => exact absurd hsr' (by simp [Event.isSnapRecv])
    | electionTimeout => exact absurd hsr' (by simp [Event.isSnapRecv])
    | heartbeatTimeout => exact absurd hsr' (by simp [Event.isSnapRecv])
    | recv src m =>
        cases m with
        | requestVote _ _ _ _ => exact absurd hsr' (by simp [Event.isSnapRecv])
        | requestVoteResp _ _ => exact absurd hsr' (by simp [Event.isSnapRecv])
        | appendEntries _ _ _ _ _ _ => exact absurd hsr' (by simp [Event.isSnapRecv])
        | appendEntriesResp _ _ _ => exact absurd hsr' (by simp [Event.isSnapRecv])
        | installSnapshot term lid lastIdx anchor pairs =>
            by_cases hi : Protocol.snapInstalls (w.nodes i) term lastIdx anchor = true
            · exact Or.inr (Or.inr (Or.inr ⟨src, term, lid, lastIdx, anchor, pairs, rfl, hi,
                by have := snapInstalls_facts hi; omega⟩))
            · exact Or.inl (by rw [Protocol.fullStep, if_neg hi])

/-- A leader's logical log only ever grows, in the world too. -/
theorem world_full_of_leader (w : World σ κ) (i : Nat) (ev : Event)
    (hlold : (w.nodes i).role = Role.leader)
    (hl : (Protocol.step (w.nodes i) ev).1.role = Role.leader) :
    fullStep w i ev = w.full i ∨ ∃ e, fullStep w i ev = LogStore.append (w.full i) e := by
  by_cases hsr : ev.isSnapRecv = false
  · rw [fullStep_node w i ev hsr]
    exact step_full_of_leader (w.nodes i) (w.full i) ev hlold hl
  · -- a snapshot demotes unless it is stale, and a stale one changes nothing
    left
    have hsr' : ev.isSnapRecv = true := by simpa using hsr
    cases ev with
    | clientReq _ _ => exact absurd hsr' (by simp [Event.isSnapRecv])
    | electionTimeout => exact absurd hsr' (by simp [Event.isSnapRecv])
    | heartbeatTimeout => exact absurd hsr' (by simp [Event.isSnapRecv])
    | recv src m =>
        cases m with
        | requestVote _ _ _ _ => exact absurd hsr' (by simp [Event.isSnapRecv])
        | requestVoteResp _ _ => exact absurd hsr' (by simp [Event.isSnapRecv])
        | appendEntries _ _ _ _ _ _ => exact absurd hsr' (by simp [Event.isSnapRecv])
        | appendEntriesResp _ _ _ => exact absurd hsr' (by simp [Event.isSnapRecv])
        | installSnapshot term lid lastIdx anchor pairs =>
            by_cases hlt : term < (w.nodes i).currentTerm
            · have hno : Protocol.snapInstalls (w.nodes i) term lastIdx anchor = false := by
                rw [Protocol.snapInstalls]; simp [hlt]
              rw [Protocol.fullStep, if_neg (by simp [hno])]
            · exfalso
              rw [Protocol.step,
                handleInstallSnapshot_follower _ _ _ _ _ _ hlt] at hl
              exact Role.noConfusion hl

/-! ## The bridge invariant -/

theorem act_snapLogs (w : World σ κ) (j : Nat) (ev : Event) :
    (w.act j ev).snapLogs
      = w.snapLogs
        ++ snapLogOf j (Protocol.step (w.nodes j) ev).1 (fullStep w j ev) :=
  rfl


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
  /--
  The log's window starts exactly at the snapshot: the snapshotted entry itself
  is kept, as the anchor replication will be resumed from.

  This is what makes a restart sound in the presence of compaction: the node
  comes back with the state machine the snapshot holds, at `snapIndex`, and
  every entry it still has to replay is still in the log.
  -/
  snapFirst : ∀ i, LogStore.firstIndex (w.nodes i).log = max 1 (w.nodes i).snapIndex
  /--
  A snapshot is either absent or at index `2` or beyond.

  At `snapIndex = 1` the window would still start at `1`, and a payload anchored
  at the virtual index `0` would be free to overwrite the snapshotted entry. Both
  `compactTo` and the snapshot installer refuse to go there.
  -/
  snapTwo : ∀ i, (w.nodes i).snapIndex = 0 ∨ 2 ≤ (w.nodes i).snapIndex
  /-- The snapshot never covers more than has been applied... -/
  snapApplied : ∀ i, (w.nodes i).snapIndex ≤ (w.nodes i).lastApplied
  /-- ...and nothing is applied that is not committed. -/
  applied : ∀ i, (w.nodes i).lastApplied ≤ (w.nodes i).commitIndex
  /--
  Every recorded leader snapshot carries a logical log, which has discarded
  nothing — it *is* a logical log, copied out of `World.full`.

  This is what a follower installing a snapshot inherits, and the reason the
  installed logical log still satisfies `first`.
  -/
  slFirst : ∀ i T n ps lg, (i, T, n, ps, lg) ∈ w.snapLogs → LogStore.firstIndex lg = 1
  /--
  **Snapshot provenance.** Every snapshot on the wire has a matching record, with
  the anchor really being the sender's entry at that index.

  This is what makes the ghost update well defined: a follower installing a
  snapshot takes a prefix of *this* log, and the record is immutable, so the
  argument does not depend on where the sender has got to since. It is
  established at the moment the snapshot is sent — the sender is a leader, so it
  records — and both lists only grow, so it is never lost.
  -/
  snapWire : ∀ src dst term lid lastIdx (anchor : Entry) (pairs : List (String × String)),
    (src, dst, Msg.installSnapshot term lid lastIdx anchor pairs) ∈ w.sent →
    ∃ lg : σ, (src, term, lastIdx, pairs, lg) ∈ w.snapLogs
      ∧ LogStore.get lg lastIdx = some anchor

theorem fullBridge_init (members : List Nat) :
    FullBridge (σ := σ) (κ := κ) (World.init members) where
  first := fun _ => LawfulLogStore.first_empty
  last := fun _ => rfl
  agree := fun _ _ _ => rfl
  window := fun _ => Or.inl LawfulLogStore.first_empty
  snapFirst := fun _ => by
    show LogStore.firstIndex (LogStore.empty : σ) = _
    rw [LawfulLogStore.first_empty]; rfl
  snapTwo := fun _ => Or.inl rfl
  snapApplied := fun _ => Nat.le_refl _
  applied := fun _ => Nat.le_refl _
  slFirst := by intro i T n ps lg h; simp [World.init] at h
  snapWire := by intro src dst term lid lastIdx anchor pairs h; simp [World.init] at h

/--
**What installing a snapshot does to the receiver.**

The three things the bridge needs: the node ends up holding exactly the anchor,
at the index the snapshot covers; its logical log becomes the sender's recorded
log cut there; and the two agree.
-/
theorem snapInstall_facts {w : World σ κ} {j src term lid lastIdx : Nat} {anchor : Entry}
    {pairs : List (String × String)}
    (h : FullBridge w)
    (hmem : (src, j, Msg.installSnapshot term lid lastIdx anchor pairs) ∈ w.sent)
    (hi : Protocol.snapInstalls (w.nodes j) term lastIdx anchor = true) :
    ∃ lg : σ, (src, term, lastIdx, pairs, lg) ∈ w.snapLogs
      ∧ LogStore.get lg lastIdx = some anchor
      ∧ LogStore.firstIndex lg = 1
      ∧ fullStep w j (.recv src (Msg.installSnapshot term lid lastIdx anchor pairs))
          = LogStore.truncFrom lg (lastIdx + 1) := by
  obtain ⟨lg, hrec, hget⟩ := h.snapWire src j term lid lastIdx anchor pairs hmem
  have hex : ∃ lg : σ, (src, term, lastIdx, pairs, lg) ∈ w.snapLogs
      ∧ LogStore.get lg lastIdx = some anchor := ⟨lg, hrec, hget⟩
  have hsel : Protocol.snapSource w src term lastIdx anchor pairs = hex.choose := by
    rw [Protocol.snapSource, dif_pos hex]
  refine ⟨Protocol.snapSource w src term lastIdx anchor pairs, ?_, ?_, ?_, ?_⟩
  · rw [hsel]; exact hex.choose_spec.1
  · rw [hsel]; exact hex.choose_spec.2
  · rw [hsel]; exact h.slFirst _ _ _ _ _ hex.choose_spec.1
  · rw [Protocol.fullStep, if_pos hi]

theorem fullBridge_step {members : List Nat} {w w' : World σ κ}
    (h : FullBridge w) (hs : Step members w w') : FullBridge w' := by
  have key : ∀ (j : Nat) (ev : Event),
      (∀ src m, ev = Event.recv src m → (src, j, m) ∈ w.sent) →
      FullBridge (w.act j ev) := by
    intro j ev hdel
    -- Everything about the acting node, in the seven shapes the clauses need.
    have main : LogStore.firstIndex (fullStep w j ev) = 1
        ∧ LogStore.lastIndex (fullStep w j ev)
            = LogStore.lastIndex (Protocol.step (w.nodes j) ev).1.log
        ∧ (∀ k, LogStore.firstIndex (Protocol.step (w.nodes j) ev).1.log ≤ k →
            LogStore.get (Protocol.step (w.nodes j) ev).1.log k
              = LogStore.get (fullStep w j ev) k)
        ∧ (LogStore.firstIndex (Protocol.step (w.nodes j) ev).1.log = 1
            ∨ LogStore.firstIndex (Protocol.step (w.nodes j) ev).1.log
              ≤ LogStore.lastIndex (Protocol.step (w.nodes j) ev).1.log)
        ∧ LogStore.firstIndex (Protocol.step (w.nodes j) ev).1.log
            = max 1 (Protocol.step (w.nodes j) ev).1.snapIndex
        ∧ ((Protocol.step (w.nodes j) ev).1.snapIndex = 0
            ∨ 2 ≤ (Protocol.step (w.nodes j) ev).1.snapIndex)
        ∧ (Protocol.step (w.nodes j) ev).1.snapIndex
            ≤ (Protocol.step (w.nodes j) ev).1.lastApplied := by
      by_cases hsr : ev.isSnapRecv = false
      · -- Away from snapshots the logical log takes the node's own operation,
        -- and nothing moves the window.
        have hlog3 : LogStore.firstIndex (fullStep w j ev) = 1
            ∧ LogStore.lastIndex (fullStep w j ev)
                = LogStore.lastIndex (Protocol.step (w.nodes j) ev).1.log
            ∧ ∀ k, LogStore.firstIndex (Protocol.step (w.nodes j) ev).1.log ≤ k →
                LogStore.get (Protocol.step (w.nodes j) ev).1.log k
                  = LogStore.get (fullStep w j ev) k := by
          have hunchanged : ∀ (ev' : Event),
              (Protocol.step (w.nodes j) ev').1.log = (w.nodes j).log →
              fullStep w j ev' = w.full j →
              LogStore.firstIndex (fullStep w j ev') = 1
                ∧ LogStore.lastIndex (fullStep w j ev')
                    = LogStore.lastIndex (Protocol.step (w.nodes j) ev').1.log
                ∧ ∀ k, LogStore.firstIndex (Protocol.step (w.nodes j) ev').1.log ≤ k →
                    LogStore.get (Protocol.step (w.nodes j) ev').1.log k
                      = LogStore.get (fullStep w j ev') k := by
            intro ev' hn hf
            rw [hn, hf]
            exact ⟨h.first j, h.last j, h.agree j⟩
          have hnode : fullStep w j ev = nodeFullStep (w.nodes j) (w.full j) ev :=
            fullStep_node w j ev (by simpa using hsr)
          cases ev with
          | electionTimeout =>
              refine hunchanged _ ?_ (by rw [hnode]; rfl)
              rcases step_log (w.nodes j) Event.electionTimeout with hn | ⟨_, _, hev, _⟩ |
                ⟨_, _, _, _, _, _, _, hev, _⟩ | ⟨_, _, _, _, _, _, hev, _⟩
              · exact hn
              · exact absurd hev (by simp)
              · exact absurd hev (by simp)
              · exact absurd hev (by simp)
          | heartbeatTimeout =>
              refine hunchanged _ ?_ (by rw [hnode]; rfl)
              rcases step_log (w.nodes j) Event.heartbeatTimeout with hn | ⟨_, _, hev, _⟩ |
                ⟨_, _, _, _, _, _, _, hev, _⟩ | ⟨_, _, _, _, _, _, hev, _⟩
              · exact hn
              · exact absurd hev (by simp)
              · exact absurd hev (by simp)
              · exact absurd hev (by simp)
          | clientReq rid cmd =>
              by_cases hlead : (w.nodes j).role = Role.leader
              · rw [hnode, nodeFullStep, if_pos hlead, Protocol.step,
                  handleClientReq_log hlead]
                refine ⟨by rw [LawfulLogStore.first_append]; exact h.first j, ?_, ?_⟩
                · rw [LogStore.lastIndex_append, LogStore.lastIndex_append, h.last j]
                · intro k hk
                  rw [LawfulLogStore.first_append] at hk
                  rw [LogStore.get_append, LogStore.get_append, h.last j]
                  split
                  · rfl
                  · exact h.agree j k hk
              · refine hunchanged _ ?_ (by rw [hnode, nodeFullStep, if_neg hlead])
                rw [Protocol.step, handleClientReq, if_pos (by simp [hlead])]
          | recv src m =>
              cases m with
              | installSnapshot a b c d e => exact absurd hsr (by simp [Event.isSnapRecv])
              | requestVote a b c d =>
                  refine hunchanged _ ?_ (by rw [hnode]; rfl)
                  rcases step_log (w.nodes j) (Event.recv src (Msg.requestVote a b c d))
                    with hn | ⟨_, _, hev, _⟩ | ⟨_, _, _, _, _, _, _, hev, _⟩ |
                    ⟨_, _, _, _, _, _, hev, _⟩
                  · exact hn
                  · exact absurd hev (by simp)
                  · exact absurd hev (by simp)
                  · exact absurd hev (by simp)
              | requestVoteResp a b =>
                  refine hunchanged _ ?_ (by rw [hnode]; rfl)
                  rcases step_log (w.nodes j) (Event.recv src (Msg.requestVoteResp a b))
                    with hn | ⟨_, _, hev, _⟩ | ⟨_, _, _, _, _, _, _, hev, _⟩ |
                    ⟨_, _, _, _, _, _, hev, _⟩
                  · exact hn
                  · exact absurd hev (by simp)
                  · exact absurd hev (by simp)
                  · exact absurd hev (by simp)
              | appendEntriesResp a b c =>
                  refine hunchanged _ ?_ (by rw [hnode]; rfl)
                  rcases step_log (w.nodes j) (Event.recv src (Msg.appendEntriesResp a b c))
                    with hn | ⟨_, _, hev, _⟩ | ⟨_, _, _, _, _, _, _, hev, _⟩ |
                    ⟨_, _, _, _, _, _, hev, _⟩
                  · exact hn
                  · exact absurd hev (by simp)
                  · exact absurd hev (by simp)
                  · exact absurd hev (by simp)
              | appendEntries term l pi pt es lc =>
                  by_cases ha : Protocol.aeAccepts (w.nodes j) term pi pt = true
                  · obtain ⟨_, _, hfw⟩ := aeAccepts_facts ha
                    rw [hnode, nodeFullStep, if_pos ha, Protocol.step,
                      handleAppendEntries_accepts, if_pos ha]
                    exact appendFrom_bridge es (w.nodes j).log (w.full j) (pi + 1) hfw
                      (h.first j) (h.last j) (h.agree j)
                  · refine hunchanged _ ?_ (by rw [hnode, nodeFullStep, if_neg ha])
                    rw [Protocol.step, handleAppendEntries_accepts, if_neg ha]
        have hsr' : ev.isSnapRecv = false := by simpa using hsr
        refine ⟨hlog3.1, hlog3.2.1, hlog3.2.2, ?_, ?_, ?_, ?_⟩
        · rcases step_log (w.nodes j) ev with hn | ⟨rid, cmd, _, hn⟩ |
            ⟨src, term, l, pi, pt, es, lc, hev', hn, hpi, hchk, hfw, _, _⟩ |
            ⟨src, term, lid, lastIdx, anchor, pairs, hev', _⟩
          · rw [hn]; exact h.window j
          · rw [hn, LawfulLogStore.first_append, LogStore.lastIndex_append]
            rcases h.window j with hc | hc
            · exact Or.inl hc
            · exact Or.inr (by omega)
          · rw [hn, appendFrom_firstIndex es (w.nodes j).log (pi + 1) hfw]
            have hge := appendFrom_lastIndex_ge es (w.nodes j).log (pi + 1) (by omega)
            rcases Classical.em (LogStore.firstIndex (w.nodes j).log = 1) with hc | hc
            · exact Or.inl hc
            · refine Or.inr ?_
              have hpos : pi ≠ 0 := by
                intro hz
                subst hz
                exact hc (Nat.le_antisymm hfw (LawfulLogStore.first_pos _))
              have := LogStore.firstIndex_le_of_termAt (hchk hpos)
              omega
          · exact absurd hsr' (by rw [hev']; simp [Event.isSnapRecv])
        · rw [step_firstIndex _ _ hsr', step_snapIndex _ _ hsr']; exact h.snapFirst j
        · rw [step_snapIndex _ _ hsr']; exact h.snapTwo j
        · rw [step_snapIndex _ _ hsr']
          have hmono := step_lastApplied_mono (w.nodes j) ev (h.applied j)
          have := h.snapApplied j
          omega
      · -- A snapshot. Either it is installed, and the node ends up holding
        -- exactly the anchor with the sender's prefix behind it, or nothing
        -- about the log moves at all.
        have hsr' : ev.isSnapRecv = true := by simpa using hsr
        cases ev with
        | clientReq _ _ => exact absurd hsr' (by simp [Event.isSnapRecv])
        | electionTimeout => exact absurd hsr' (by simp [Event.isSnapRecv])
        | heartbeatTimeout => exact absurd hsr' (by simp [Event.isSnapRecv])
        | recv src m =>
            cases m with
            | requestVote _ _ _ _ => exact absurd hsr' (by simp [Event.isSnapRecv])
            | requestVoteResp _ _ => exact absurd hsr' (by simp [Event.isSnapRecv])
            | appendEntries _ _ _ _ _ _ =>
                exact absurd hsr' (by simp [Event.isSnapRecv])
            | appendEntriesResp _ _ _ =>
                exact absurd hsr' (by simp [Event.isSnapRecv])
            | installSnapshot term lid lastIdx anchor pairs =>
                by_cases hi : Protocol.snapInstalls (w.nodes j) term lastIdx anchor = true
                · obtain ⟨hlt2, hlow, hcom⟩ := snapInstalls_facts hi
                  obtain ⟨lg, _, hget, hlg1, hfl⟩ :=
                    snapInstall_facts h (hdel src _ rfl) hi
                  have hlgreach : lastIdx ≤ LogStore.lastIndex lg :=
                    ((LogStore.get_isSome_iff lg lastIdx).mp (by rw [hget]; rfl)).2
                  obtain ⟨hlog, hrole, hsnapi, hla, hci⟩ :
                      (Protocol.step (w.nodes j)
                          (.recv src (Msg.installSnapshot term lid lastIdx anchor pairs))).1.log
                          = LogStore.fromAnchor lastIdx anchor
                        ∧ (Protocol.step (w.nodes j)
                          (.recv src (Msg.installSnapshot term lid lastIdx anchor pairs))).1.role
                          = Role.follower
                        ∧ (Protocol.step (w.nodes j)
                          (.recv src (Msg.installSnapshot term lid lastIdx anchor pairs))).1.snapIndex
                          = lastIdx
                        ∧ (Protocol.step (w.nodes j)
                          (.recv src (Msg.installSnapshot term lid lastIdx anchor pairs))).1.lastApplied
                          = lastIdx
                        ∧ (Protocol.step (w.nodes j)
                          (.recv src (Msg.installSnapshot term lid lastIdx anchor pairs))).1.commitIndex
                          = lastIdx := by
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
                      (rw [Protocol.step, handleInstallSnapshot, if_neg hlt2]
                       dsimp only
                       rw [if_pos hi])
                  rw [hfl, hlog, hsnapi, hla]
                  refine ⟨by rw [LawfulLogStore.first_truncFrom, hlg1]; omega, ?_, ?_,
                    ?_, ?_, Or.inr hlow, Nat.le_refl _⟩
                  · rw [LogStore.lastIndex_fromAnchor, LogStore.lastIndex_truncFrom]; omega
                  · intro k hk
                    rw [LogStore.firstIndex_fromAnchor] at hk
                    rw [LogStore.get_fromAnchor, LogStore.get_truncFrom]
                    by_cases hkk : k = max 1 lastIdx
                    · rw [if_pos hkk, if_pos (by omega), show k = lastIdx by omega]
                      exact hget.symm
                    · rw [if_neg hkk, if_neg (by omega)]
                  · rw [LogStore.firstIndex_fromAnchor, LogStore.lastIndex_fromAnchor]
                    exact Or.inr (Nat.le_refl _)
                  · rw [LogStore.firstIndex_fromAnchor]
                · have hi' : Protocol.snapInstalls (w.nodes j) term lastIdx anchor = false := by
                    simpa using hi
                  obtain ⟨hlog, hsnapi, hla, hci⟩ :=
                    handleInstallSnapshot_noop (w.nodes j) term lid lastIdx anchor pairs hi'
                  have hfl : fullStep w j
                      (.recv src (Msg.installSnapshot term lid lastIdx anchor pairs))
                      = w.full j := by rw [Protocol.fullStep, if_neg hi]
                  rw [hfl]
                  show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
                  rw [Protocol.step]
                  rw [hlog, hsnapi, hla]
                  exact ⟨h.first j, h.last j, h.agree j, h.window j, h.snapFirst j,
                    h.snapTwo j, h.snapApplied j⟩
    refine ⟨fun i => ?_, fun i => ?_, fun i k hk => ?_, fun i => ?_, fun i => ?_,
      fun i => ?_, fun i => ?_, fun i => ?_, fun a b c d e hm => ?_,
      fun a b c d e f g hm => ?_⟩
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
        exact main.2.2.1 k hk
      · rw [act_nodes_ne _ _ _ hij] at hk
        rw [act_full_ne _ _ _ hij, act_nodes_ne _ _ _ hij]
        exact h.agree i k hk
    · by_cases hij : i = j
      · subst hij; rw [act_nodes_self]; exact main.2.2.2.1
      · rw [act_nodes_ne _ _ _ hij]; exact h.window i
    · by_cases hij : i = j
      · subst hij; rw [act_nodes_self]; exact main.2.2.2.2.1
      · rw [act_nodes_ne _ _ _ hij]; exact h.snapFirst i
    · by_cases hij : i = j
      · subst hij; rw [act_nodes_self]; exact main.2.2.2.2.2.1
      · rw [act_nodes_ne _ _ _ hij]; exact h.snapTwo i
    · by_cases hij : i = j
      · subst hij; rw [act_nodes_self]; exact main.2.2.2.2.2.2
      · rw [act_nodes_ne _ _ _ hij]; exact h.snapApplied i
    · by_cases hij : i = j
      · subst hij; rw [act_nodes_self]; exact step_applied_le _ _ (h.applied i)
      · rw [act_nodes_ne _ _ _ hij]; exact h.applied i
    · rw [act_snapLogs] at hm
      rcases List.mem_append.mp hm with hm' | hm'
      · exact h.slFirst a b c d e hm'
      · rw [snapLogOf] at hm'
        split at hm'
        · rcases List.mem_singleton.mp hm' with hq
          have : e = fullStep w j ev := by
            have hq2 := congrArg (fun r => r.2.2.2.2) hq
            simpa using hq2
          rw [this]; exact main.1
        · simp at hm'
    · -- **Provenance.** A snapshot newly on the wire came from a leader, which
      -- recorded at that very step; and the anchor it carries is that node's own
      -- entry, which the bridge says the logical log holds too.
      rw [act_sent] at hm
      rcases List.mem_append.mp hm with hm' | hm'
      · obtain ⟨lg, h1, h2⟩ := h.snapWire a b c d e f g hm'
        exact ⟨lg, by rw [act_snapLogs]; exact List.mem_append_left _ h1, h2⟩
      · rcases mem_sendsOf hm' with ⟨to, m0, heq, hact⟩
        have h1 : a = j := congrArg (fun q => q.1) heq
        have hm0 : m0 = Msg.installSnapshot c d e f g := by
          have := congrArg (fun q => q.2.2) heq; simpa using this.symm
        subst hm0; subst h1
        obtain ⟨ht, hli, hanc, hps, hfne, hlog, hsi, hskv, hct, hns, hnf⟩ :=
          step_installSnapshot_payload hact
        -- the anchor is the sender's own entry, which its logical log holds
        have hf2 := h.snapFirst a
        have hw2 := h.window a
        have hne : LogStore.firstIndex (w.nodes a).log ≤ (w.nodes a).snapIndex := by omega
        have hsome : (LogStore.get (w.nodes a).log (w.nodes a).snapIndex).isSome := by
          refine LawfulLogStore.get_isSome _ _ hne ?_
          have hsz : LogStore.size (w.nodes a).log = LogStore.lastIndex (w.nodes a).log := rfl
          rcases hw2 with hc | hc
          · omega
          · rw [hsz]; omega
        have hagree := h.agree a (w.nodes a).snapIndex hne
        refine ⟨fullStep w a ev, ?_, ?_⟩
        · rw [act_snapLogs]
          refine List.mem_append_right _ ?_
          rw [snapLogOf, if_pos ?_]
          · rw [ht, hli, hps]
            refine List.mem_singleton.mpr ?_
            rw [hct, hsi, hskv]
          · exact (step_installSnapshot_leader hact).1
        · have hfl : fullStep w a ev = w.full a := by
            rw [fullStep_node w a ev hns]; exact hnf (w.full a)
          rw [hfl, hli, hanc, ← hagree]
          cases hq : LogStore.get (w.nodes a).log (w.nodes a).snapIndex with
          | none => rw [hq] at hsome; simp at hsome
          | some x => rfl
  cases hs with
  | deliver s d m hd hmem =>
      refine key d _ ?_
      intro src' m' heq
      have h1 : s = src' := (Event.recv.inj heq).1
      have h2 : m = m' := (Event.recv.inj heq).2
      subst h2; subst h1; exact hmem
  | electionTimeout k hk => exact key k _ (fun _ _ hq => Event.noConfusion hq)
  | heartbeat k hk => exact key k _ (fun _ _ hq => Event.noConfusion hq)
  | client k rid cmd hk => exact key k _ (fun _ _ hq => Event.noConfusion hq)
  | crash k hk =>
      -- the durable trio survives, and the state machine restarts from the snapshot
      refine ⟨fun i => ?_, fun i => ?_, fun i k' hk' => ?_, fun i => ?_, fun i => ?_,
        fun i => ?_, fun i => ?_, fun i => ?_, fun a b c d e hm => ?_,
        fun a b c d e f g hm => ?_⟩
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
      · by_cases hij : i = k
        · subst hij; rw [crash_nodes_self, restart_log, restart_snapIndex]; exact h.snapFirst i
        · rw [crash_nodes_ne _ _ hij]; exact h.snapFirst i
      · by_cases hij : i = k
        · subst hij; rw [crash_nodes_self, restart_snapIndex]; exact h.snapTwo i
        · rw [crash_nodes_ne _ _ hij]; exact h.snapTwo i
      · by_cases hij : i = k
        · subst hij
          rw [crash_nodes_self, restart_snapIndex, restart_lastApplied]
          exact Nat.le_refl _
        · rw [crash_nodes_ne _ _ hij]; exact h.snapApplied i
      · by_cases hij : i = k
        · subst hij
          rw [crash_nodes_self, restart_lastApplied, restart_commitIndex]
          exact Nat.le_refl _
        · rw [crash_nodes_ne _ _ hij]; exact h.applied i
      · rw [crash_snapLogs] at hm; exact h.slFirst a b c d e hm
      · rw [crash_sent] at hm; exact h.snapWire a b c d e f g hm
  | compact k hk =>
      -- **The compaction case.** The logical log does not move at all, so the
      -- only thing to check is that the node still holds everything above the
      -- window it just moved forward.
      have hmain : ∀ i, i = k →
          LogStore.firstIndex ((Protocol.compactTo (w.nodes i)).log)
              = max 1 (Protocol.compactTo (w.nodes i)).snapIndex
            ∧ ((Protocol.compactTo (w.nodes i)).snapIndex = 0
              ∨ 2 ≤ (Protocol.compactTo (w.nodes i)).snapIndex)
            ∧ (Protocol.compactTo (w.nodes i)).snapIndex
              ≤ (Protocol.compactTo (w.nodes i)).lastApplied
            ∧ LogStore.lastIndex (w.full i)
              = LogStore.lastIndex ((Protocol.compactTo (w.nodes i)).log)
            ∧ (∀ q, LogStore.firstIndex ((Protocol.compactTo (w.nodes i)).log) ≤ q →
                LogStore.get ((Protocol.compactTo (w.nodes i)).log) q
                  = LogStore.get (w.full i) q)
            ∧ (LogStore.firstIndex ((Protocol.compactTo (w.nodes i)).log) = 1
              ∨ LogStore.firstIndex ((Protocol.compactTo (w.nodes i)).log)
                ≤ LogStore.lastIndex ((Protocol.compactTo (w.nodes i)).log)) := by
        intro i _
        rw [Protocol.compactTo]
        split
        · rename_i hg
          obtain ⟨hg0, hg1, hg2⟩ := hg
          have hfi := LogStore.firstIndex_compact (w.nodes i).log ((w.nodes i).lastApplied)
            hg1 hg2
          have hli := LogStore.lastIndex_compact (w.nodes i).log ((w.nodes i).lastApplied)
            hg1 hg2
          refine ⟨by show LogStore.firstIndex (LogStore.compact _ _) = _; rw [hfi]; simp; omega,
            by simp; omega, by simp, ?_, ?_, ?_⟩
          · show LogStore.lastIndex (w.full i)
              = LogStore.lastIndex (LogStore.compact (w.nodes i).log ((w.nodes i).lastApplied))
            rw [hli]; exact h.last i
          · intro q hq
            show LogStore.get (LogStore.compact (w.nodes i).log ((w.nodes i).lastApplied)) q
              = LogStore.get (w.full i) q
            have hq' : (w.nodes i).lastApplied ≤ q := by
              have hx : LogStore.firstIndex
                  (LogStore.compact (w.nodes i).log ((w.nodes i).lastApplied)) ≤ q := hq
              rw [hfi] at hx; exact hx
            rw [LogStore.get_compact_of_le _ _ _ hg1 hg2 hq']
            exact h.agree i q (by omega)
          · right
            show LogStore.firstIndex (LogStore.compact _ _) ≤ LogStore.lastIndex (LogStore.compact _ _)
            rw [hfi, hli]; omega
        · exact ⟨h.snapFirst i, h.snapTwo i, h.snapApplied i, h.last i, h.agree i, h.window i⟩
      refine ⟨fun i => ?_, fun i => ?_, fun i q hq => ?_, fun i => ?_, fun i => ?_,
        fun i => ?_, fun i => ?_, fun i => ?_, fun a b c d e hm => ?_,
        fun a b c d e f g hm => ?_⟩
      · rw [compactAt_full]; exact h.first i
      · rw [compactAt_full]
        by_cases hij : i = k
        · subst hij; rw [compactAt_nodes_self]; exact (hmain i rfl).2.2.2.1
        · rw [compactAt_nodes_ne _ _ hij]; exact h.last i
      · rw [compactAt_full]
        by_cases hij : i = k
        · subst hij
          rw [compactAt_nodes_self] at hq ⊢
          exact (hmain i rfl).2.2.2.2.1 q hq
        · rw [compactAt_nodes_ne _ _ hij] at hq ⊢; exact h.agree i q hq
      · by_cases hij : i = k
        · subst hij; rw [compactAt_nodes_self]; exact (hmain i rfl).2.2.2.2.2
        · rw [compactAt_nodes_ne _ _ hij]; exact h.window i
      · by_cases hij : i = k
        · subst hij; rw [compactAt_nodes_self]; exact (hmain i rfl).1
        · rw [compactAt_nodes_ne _ _ hij]; exact h.snapFirst i
      · by_cases hij : i = k
        · subst hij; rw [compactAt_nodes_self]; exact (hmain i rfl).2.1
        · rw [compactAt_nodes_ne _ _ hij]; exact h.snapTwo i
      · by_cases hij : i = k
        · subst hij; rw [compactAt_nodes_self]; exact (hmain i rfl).2.2.1
        · rw [compactAt_nodes_ne _ _ hij]; exact h.snapApplied i
      · by_cases hij : i = k
        · subst hij; rw [compactAt_nodes_self, compactTo_lastApplied, compactTo_commitIndex]
          exact h.applied i
        · rw [compactAt_nodes_ne _ _ hij]; exact h.applied i
      · rw [compactAt_snapLogs] at hm; exact h.slFirst a b c d e hm
      · rw [compactAt_sent] at hm; exact h.snapWire a b c d e f g hm

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

/-- The term read off either log at an index the real one can be asked about. -/
theorem full_termAt_getD {members : List Nat} {w : World σ κ} (h : Reachable members w)
    {i k : Nat} (hk : k = 0 ∨ LogStore.firstIndex (w.nodes i).log ≤ k) :
    (LogStore.termAt (w.full i) k).getD 0 = (LogStore.termAt (w.nodes i).log k).getD 0 := by
  rcases hk with hz | hf
  · subst hz
    unfold LogStore.termAt
    rw [LogStore.get_zero, LogStore.get_zero]
  · unfold LogStore.termAt
    rw [full_get h hf]

/-- The two logs reach exactly as far as each other. -/
theorem full_lastIndex {members : List Nat} {w : World σ κ} (h : Reachable members w) (i : Nat) :
    LogStore.lastIndex (w.full i) = LogStore.lastIndex (w.nodes i).log :=
  (fullBridge_reachable h).last i

/-- A leader's logical log only grows across a step, mirroring `leader_log_monotone`. -/
theorem leader_full_monotone {members : List Nat} {w w' : World σ κ}
    (hs : Step members w w') {i : Nat}
    (hl : (w.nodes i).role = Role.leader) (hl' : (w'.nodes i).role = Role.leader) :
    w'.full i = w.full i ∨ ∃ e, w'.full i = LogStore.append (w.full i) e := by
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev →
      w'.full i = w.full i ∨ ∃ e, w'.full i = LogStore.append (w.full i) e := by
    intro j ev hw
    subst hw
    by_cases hij : i = j
    · subst hij
      rw [act_nodes_self] at hl'
      rw [act_full_self]
      exact world_full_of_leader w i ev hl hl'
    · rw [act_full_ne _ _ _ hij]; exact Or.inl rfl
  cases hs with
  | deliver s d m hd hmem => exact key d _ rfl
  | electionTimeout k _ => exact key k _ rfl
  | heartbeat k _ => exact key k _ rfl
  | client k rid cmd _ => exact key k _ rfl
  | crash k _ => exact Or.inl rfl
  | compact k _ => exact Or.inl rfl
/-- Nothing a node still has to apply has been discarded. -/
theorem full_applied {members : List Nat} {w : World σ κ} (h : Reachable members w) (i : Nat) :
    LogStore.firstIndex (w.nodes i).log ≤ (w.nodes i).lastApplied + 1 := by
  have h1 := (fullBridge_reachable h).snapFirst i
  have h2 := (fullBridge_reachable h).snapApplied i
  omega

/-- The snapshot never covers more than has been applied. -/
theorem full_snapIndex {members : List Nat} {w : World σ κ} (h : Reachable members w) (i : Nat) :
    (w.nodes i).snapIndex ≤ (w.nodes i).lastApplied := (fullBridge_reachable h).snapApplied i

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
