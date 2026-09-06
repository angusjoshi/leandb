import RaftKV.Proof.Created

/-!
# Real logs hold only created entries

`entry_unique` is about the ghost `created` list. To say anything about actual
replicas we need the bridge: **every entry in any node's log, and every entry in
any `appendEntries` payload on the wire, was minted by some leader at that
index.**

Both directions of the bridge are needed at once, and that is why they are
proved together: log entries enter a follower's log from a message payload, and
a message payload is drawn from the sender's log.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [LawfulLogStore σ] [KVStore κ]

/-- Every entry in a node's log was created at that index. -/
def LogFromCreated (w : World σ κ) : Prop :=
  ∀ i k e, LogStore.get (w.nodes i).log k = some e → ∃ c, (c, k, e) ∈ w.created

/-- Every entry in a replication payload was created at its intended index. -/
def MsgFromCreated (w : World σ κ) : Prop :=
  ∀ src dst t l pi pt es lc n e,
    (src, dst, Msg.appendEntries t l pi pt es lc) ∈ w.sent → es[n]? = some e →
    ∃ c, (c, pi + 1 + n, e) ∈ w.created

/-- The bridge invariants. -/
structure BInv (members : List Nat) (w : World σ κ) : Prop where
  /-- Logs hold only created entries. -/
  logs : LogFromCreated w
  /-- Payloads carry only created entries. -/
  msgs : MsgFromCreated w

theorem bInv_init (members : List Nat) :
    BInv (σ := σ) (κ := κ) members (World.init members) where
  logs := by
    intro i k e h
    rw [World.init] at h
    simp only [Protocol.initState] at h
    have hs := (LogStore.get_isSome_iff (LogStore.empty : σ) k).mp (by rw [h]; rfl)
    simp only [LogStore.lastIndex_empty] at hs
    omega
  msgs := by intro src dst t l pi pt es lc n e h; simp [World.init] at h

/-- A leader's payload is exactly a tail of its own log. -/
theorem appendEntriesTo_entries {s : NodeState σ κ} {p n : Nat} {e : Entry}
    (h : (LogStore.sliceFrom s.log
            (max 1 (PeerMap.get s.nextIndex p (LogStore.lastIndex s.log + 1))))[n]? = some e) :
    LogStore.get s.log
      (max 1 (PeerMap.get s.nextIndex p (LogStore.lastIndex s.log + 1)) + n) = some e := by
  rwa [LogStore.getElem?_sliceFrom s.log _ n (Nat.le_max_left 1 _)] at h

/-- Membership in `created` survives a step. -/
theorem created_mono {w : World σ κ} {j : Nat} {ev : Event} {c k : Nat} {e : Entry}
    (h : (c, k, e) ∈ w.created) : (c, k, e) ∈ (w.act j ev).created := by
  rw [act_created]; exact List.mem_append_left _ h

/-- **The bridge invariants are preserved by every step.** -/
theorem bInv_step {members : List Nat} {w w' : World σ κ}
    (h : BInv members w) (hs : Step members w w') : BInv members w' := by
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev →
      (∀ src m', ev = Event.recv src m' → (src, j, m') ∈ w.sent) →
      BInv members w' := by
    intro j ev hw hdel
    subst hw
    -- Logs first: a spliced entry comes from the payload, which is already covered.
    have hlogs : LogFromCreated (w.act j ev) := by
      intro i k e hget
      by_cases hij : i = j
      · subst hij
        rw [act_nodes_self] at hget
        rcases step_log (w.nodes i) ev with hl | ⟨rid, cmd, hev, hl⟩ | ⟨src, term, l, pi, pt, es, lc, hev, hl, hpi, hchk, _, _⟩
        · rw [hl] at hget
          obtain ⟨c, hc⟩ := h.logs i k e hget
          exact ⟨c, created_mono hc⟩
        · -- a fresh client entry, which the ghost records
          rw [hl, LogStore.get_append] at hget
          by_cases hk : k = LogStore.lastIndex (w.nodes i).log + 1
          · rw [if_pos hk] at hget
            refine ⟨i, ?_⟩
            rw [act_created]
            refine List.mem_append_right _ ?_
            subst hev
            have hlead : (w.nodes i).role = Role.leader := by
              rcases Classical.em ((w.nodes i).role = Role.leader) with hc | hc
              · exact hc
              · exfalso
                rw [Protocol.step, handleClientReq, if_pos (by simp [hc])] at hl
                have := congrArg LogStore.lastIndex hl
                simp only [LogStore.lastIndex_append] at this
                omega
            have hpost : (Protocol.step (w.nodes i) (Event.clientReq rid cmd)).1.role
                = Role.leader := by
              rw [Protocol.step, handleClientReq, if_neg (by rw [hlead]; simp)]
              dsimp only; simp [hlead]
            have he : e = { term := (w.nodes i).currentTerm, cmd := cmd, reqId := rid } :=
              (Option.some.inj hget).symm
            unfold createdOf
            dsimp only
            rw [if_pos hpost]
            refine List.mem_singleton.mpr ?_
            have hidx : k = LogStore.lastIndex
                (Protocol.step (w.nodes i) (Event.clientReq rid cmd)).1.log := by
              rw [hk, Protocol.step, handleClientReq_log hlead, LogStore.lastIndex_append]
            have hent : e = { term := (Protocol.step (w.nodes i)
                (Event.clientReq rid cmd)).1.currentTerm, cmd := cmd, reqId := rid } := by
              rw [he, Protocol.step, handleClientReq_term_eq]
            rw [hidx, hent]
          · rw [if_neg hk] at hget
            obtain ⟨c, hc⟩ := h.logs i k e hget
            exact ⟨c, created_mono hc⟩
        · -- a spliced entry: either it was already there, or it came from the payload
          rw [hl] at hget
          refine appendFrom_mem (fun k' e' => ∃ c, (c, k', e') ∈ (w.act i ev).created)
            es (w.nodes i).log (pi + 1) (by omega) (by omega) ?_ ?_ k e hget
          · intro k' e' hk'
            obtain ⟨c, hc⟩ := h.logs i k' e' hk'
            exact ⟨c, created_mono hc⟩
          · intro n e' hn
            subst hev
            obtain ⟨c, hc⟩ := h.msgs src i term l pi pt es lc n e'
              (hdel src (Msg.appendEntries term l pi pt es lc) rfl) hn
            exact ⟨c, created_mono hc⟩
      · rw [act_nodes_ne _ _ _ hij] at hget
        obtain ⟨c, hc⟩ := h.logs i k e hget
        exact ⟨c, created_mono hc⟩
    refine ⟨hlogs, ?_⟩
    -- Payloads: a fresh one is drawn from the sender's post-state log.
    intro src dst t l pi pt es lc n e hp hn
    rw [act_sent] at hp
    rcases List.mem_append.mp hp with hp' | hp'
    · obtain ⟨c, hc⟩ := h.msgs src dst t l pi pt es lc n e hp' hn
      exact ⟨c, created_mono hc⟩
    · rcases mem_sendsOf hp' with ⟨to, m, heq, hact⟩
      have hsj : src = j := congrArg (fun q => q.1) heq
      have hm : m = Msg.appendEntries t l pi pt es lc := by
        have := congrArg (fun q => q.2.2) heq; simpa using this.symm
      subst hm; subst hsj
      -- the payload is `sliceFrom` of the post-state log at `pi + 1`
      have hslice : ∃ p, Msg.appendEntries t l pi pt es lc
          = appendEntriesTo (Protocol.step (w.nodes src) ev).1 p := by
        exact step_appendEntries_payload hact
      obtain ⟨p, hp2⟩ := hslice
      simp only [appendEntriesTo] at hp2
      obtain ⟨_, _, hpi, _, hes, _⟩ := Msg.appendEntries.inj hp2
      have hget : LogStore.get (Protocol.step (w.nodes src) ev).1.log (pi + 1 + n) = some e := by
        rw [hes] at hn
        have := appendEntriesTo_entries (s := (Protocol.step (w.nodes src) ev).1) (p := p) hn
        rwa [show max 1 (PeerMap.get (Protocol.step (w.nodes src) ev).1.nextIndex p
              (LogStore.lastIndex (Protocol.step (w.nodes src) ev).1.log + 1)) = pi + 1 by
          rw [hpi]; omega] at this
      exact hlogs src (pi + 1 + n) e (by rw [act_nodes_self]; exact hget)
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
  | crash k hk =>
      -- the log is durable and nothing is sent, so both halves carry over
      refine ⟨?_, ?_⟩
      · intro i k' e hget
        rw [crash_created]
        by_cases hij : i = k
        · subst hij; rw [crash_nodes_self, restart_log] at hget; exact h.logs i k' e hget
        · rw [crash_nodes_ne _ _ hij] at hget; exact h.logs i k' e hget
      · intro src dst t l pi pt es lc n e hp hn
        rw [crash_sent] at hp; rw [crash_created]
        exact h.msgs src dst t l pi pt es lc n e hp hn

/-- The bridge invariants hold in every reachable world. -/
theorem bInv_reachable {members : List Nat} {w : World σ κ} (h : Reachable members w) :
    BInv members w := by
  induction h with
  | init => exact bInv_init members
  | tail _ hs ih => exact bInv_step ih hs

/--
**Log Matching, part one, for real logs.**

In any reachable world, if two replicas hold entries at the same log index with
the same term, those entries are identical — same command, same client request.

This is the statement Raft's paper makes about logs, now carried from the ghost
`created` record onto the actual replicated state.
-/
theorem log_entry_unique {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) {i j k : Nat} {e₁ e₂ : Entry}
    (h₁ : LogStore.get (w.nodes i).log k = some e₁)
    (h₂ : LogStore.get (w.nodes j).log k = some e₂)
    (hterm : e₁.term = e₂.term) : e₁ = e₂ := by
  obtain ⟨c₁, hc₁⟩ := (bInv_reachable hrch).logs i k e₁ h₁
  obtain ⟨c₂, hc₂⟩ := (bInv_reachable hrch).logs j k e₂ h₂
  exact entry_unique hnd hrch hc₁ hc₂ hterm

end RaftKV.Proof
