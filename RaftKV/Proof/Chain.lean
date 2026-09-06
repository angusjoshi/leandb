import RaftKV.Proof.LogCreated

/-!
# The predecessor chain

`log_entry_unique` says an entry is pinned down by its index and term. This
module adds the link that turns that into agreement over *whole prefixes*: for
every minted entry, the ghost `chain` records the **term of the entry directly
beneath it**.

Because a term at an index determines the entry there, the recorded predecessor
term determines the predecessor entry. Chasing links downwards from a shared
index therefore forces two logs to agree all the way to the start — which is Log
Matching, part two.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [LawfulLogStore σ] [KVStore κ]

theorem act_chain (w : World σ κ) (j : Nat) (ev : Event) :
    (w.act j ev).chain = w.chain ++ chainOf j (Protocol.step (w.nodes j) ev).1 ev := rfl

theorem mem_chainOf {j idx p : Nat} {e : Entry} {s : NodeState σ κ} {ev : Event}
    (h : (idx, e, p) ∈ chainOf j s ev) :
    s.role = Role.leader ∧ idx = LogStore.lastIndex s.log ∧ e.term = s.currentTerm
      ∧ ∃ rid cmd, ev = Event.clientReq rid cmd := by
  unfold chainOf at h
  cases ev with
  | clientReq rid cmd =>
      dsimp only at h
      split at h
      · rename_i hr
        simp only [List.mem_singleton, Prod.mk.injEq] at h
        exact ⟨hr, h.1, by rw [h.2.1], rid, cmd, rfl⟩
      · simp at h
  | recv a b => simp at h
  | electionTimeout => simp at h
  | heartbeatTimeout => simp at h

theorem chain_mono {w : World σ κ} {j : Nat} {ev : Event} {k p : Nat} {e : Entry}
    (h : (k, e, p) ∈ w.chain) : (k, e, p) ∈ (w.act j ev).chain := by
  rw [act_chain]; exact List.mem_append_left _ h

/-- Logs have no holes: an entry at `idx` implies entries at every index below. -/
theorem get_isSome_below {lg : σ} {idx m : Nat} {e : Entry}
    (h : LogStore.get lg idx = some e) (h1 : 1 ≤ m) (hm : m ≤ idx) :
    (LogStore.get lg m).isSome := by
  have hidx := (LogStore.get_isSome_iff lg idx).mp (by rw [h]; rfl)
  exact (LogStore.get_isSome_iff lg m).mpr ⟨h1, by omega⟩

/--
Every entry in a log beyond the first has its predecessor link on record, and
that link agrees with what the log actually holds beneath it.
-/
def LogChain (w : World σ κ) : Prop :=
  ∀ i idx e, LogStore.get (w.nodes i).log idx = some e → 2 ≤ idx →
    ∃ p, (idx, e, p) ∈ w.chain ∧ LogStore.termAt (w.nodes i).log (idx - 1) = some p

/-- The same for entries carried in a replication payload. -/
def MsgChain (w : World σ κ) : Prop :=
  ∀ src dst t l pi pt es lc n e,
    (src, dst, Msg.appendEntries t l pi pt es lc) ∈ w.sent → es[n]? = some e →
    2 ≤ pi + 1 + n →
    ∃ p, (pi + 1 + n, e, p) ∈ w.chain
      ∧ (if n = 0 then p = pt else ∃ e', es[n - 1]? = some e' ∧ p = e'.term)

/-- Every chain link belongs to a minted entry. -/
def ChainCreated (w : World σ κ) : Prop :=
  ∀ idx e p, (idx, e, p) ∈ w.chain → ∃ c, (c, idx, e) ∈ w.created

/-- **An index and entry determine the recorded predecessor term.** -/
def ChainDet (w : World σ κ) : Prop :=
  ∀ idx e p₁ p₂, (idx, e, p₁) ∈ w.chain → (idx, e, p₂) ∈ w.chain → p₁ = p₂

/-- The chain invariants. -/
structure ChInv (members : List Nat) (w : World σ κ) : Prop where
  /-- Logs carry their predecessor links. -/
  logs : LogChain w
  /-- Payloads carry their predecessor links. -/
  msgs : MsgChain w
  /-- Links belong to minted entries. -/
  created : ChainCreated w
  /-- Links are determined by index and entry. -/
  det : ChainDet w

theorem chInv_init (members : List Nat) :
    ChInv (σ := σ) (κ := κ) members (World.init members) where
  logs := by
    intro i idx e h _
    exfalso
    rw [World.init] at h
    simp only [Protocol.initState] at h
    have hs := (LogStore.get_isSome_iff (LogStore.empty : σ) idx).mp (by rw [h]; rfl)
    simp only [LogStore.lastIndex_empty] at hs
    omega
  msgs := by intro src dst t l pi pt es lc n e h; simp [World.init] at h
  created := by intro idx e p h; simp [World.init] at h
  det := by intro idx e p₁ p₂ h; simp [World.init] at h

/-- **The chain invariants are preserved by every step.** -/
theorem chInv_step {members : List Nat} {w w' : World σ κ}
    (hnd : members.Nodup) (hr : Reachable members w)
    (h : ChInv members w) (hs : Step members w w') : ChInv members w' := by
  have hr' : Reachable members w' := Reachable.tail hr hs
  have hb' := bInv_reachable hr'
  have hbo := bInv_reachable hr
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev →
      (∀ src m', ev = Event.recv src m' → (src, j, m') ∈ w.sent) →
      ChInv members w' := by
    intro j ev hw hdel
    subst hw
    have hlogs : LogChain (w.act j ev) := by
      intro i idx e hget hidx
      by_cases hij : i = j
      · subst hij
        rw [act_nodes_self] at hget ⊢
        rcases step_log (w.nodes i) ev with hl | ⟨rid, cmd, hev, hl⟩ |
          ⟨src, term, l, pi, pt, es, lc, hev, hl, hpi, hchk, _, _⟩
        · rw [hl] at hget ⊢
          obtain ⟨p, hp1, hp2⟩ := h.logs i idx e hget hidx
          exact ⟨p, chain_mono hp1, hp2⟩
        · -- a client append: only the top index is new
          have hlead : (w.nodes i).role = Role.leader := by
            rcases Classical.em ((w.nodes i).role = Role.leader) with hc | hc
            · exact hc
            · exfalso
              subst hev
              rw [Protocol.step, handleClientReq, if_pos (by simp [hc])] at hl
              have := congrArg LogStore.lastIndex hl
              simp only [LogStore.lastIndex_append] at this
              omega
          rw [hl] at hget ⊢
          rw [LogStore.get_append] at hget
          by_cases hk : idx = LogStore.lastIndex (w.nodes i).log + 1
          · -- the freshly minted entry, whose link the ghost just recorded
            rw [if_pos hk] at hget
            have he : e = { term := (w.nodes i).currentTerm, cmd := cmd, reqId := rid } :=
              (Option.some.inj hget).symm
            have hprev : (LogStore.get (w.nodes i).log (idx - 1)).isSome := by
              refine (LogStore.get_isSome_iff (w.nodes i).log (idx - 1)).mpr ⟨by omega, by omega⟩
            obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hprev
            refine ⟨v.term, ?_, ?_⟩
            · rw [act_chain]
              refine List.mem_append_right _ ?_
              subst hev
              have hpost : (Protocol.step (w.nodes i) (Event.clientReq rid cmd)).1.role
                  = Role.leader := by
                rw [Protocol.step, handleClientReq, if_neg (by rw [hlead]; simp)]
                dsimp only; simp [hlead]
              unfold chainOf
              dsimp only
              rw [if_pos hpost]
              refine List.mem_singleton.mpr ?_
              have hidx' : idx = LogStore.lastIndex
                  (Protocol.step (w.nodes i) (Event.clientReq rid cmd)).1.log := by
                rw [hk, Protocol.step, handleClientReq_log hlead, LogStore.lastIndex_append]
              have hent : e = { term := (Protocol.step (w.nodes i)
                  (Event.clientReq rid cmd)).1.currentTerm, cmd := cmd, reqId := rid } := by
                rw [he, Protocol.step, handleClientReq_term_eq]
              have hterm' : v.term = (LogStore.termAt (Protocol.step (w.nodes i)
                  (Event.clientReq rid cmd)).1.log
                  (LogStore.lastIndex (Protocol.step (w.nodes i)
                    (Event.clientReq rid cmd)).1.log - 1)).getD 0 := by
                rw [← hidx', Protocol.step, handleClientReq_log hlead]
                unfold LogStore.termAt
                rw [LogStore.get_append, if_neg (by omega), hv]
                rfl
              rw [hidx', hent, hterm']
            · unfold LogStore.termAt
              rw [LogStore.get_append, if_neg (by omega), hv]
              rfl
          · rw [if_neg hk] at hget
            obtain ⟨p, hp1, hp2⟩ := h.logs i idx e hget hidx
            refine ⟨p, chain_mono hp1, ?_⟩
            unfold LogStore.termAt at hp2 ⊢
            rw [LogStore.get_append, if_neg (by
              have := ((LogStore.get_isSome_iff (w.nodes i).log idx).mp (by rw [hget]; rfl)).2
              omega)]
            exact hp2
        · -- a splice
          subst hev
          rw [hl] at hget ⊢
          have hbound : pi + 1 ≤ LogStore.lastIndex (w.nodes i).log + 1 := by omega
          by_cases hlow : idx < pi + 1
          · rw [appendFrom_get_of_lt es _ (pi + 1) idx hbound hlow] at hget
            obtain ⟨p, hp1, hp2⟩ := h.logs i idx e hget hidx
            refine ⟨p, chain_mono hp1, ?_⟩
            unfold LogStore.termAt at hp2 ⊢
            rw [appendFrom_get_of_lt es _ (pi + 1) (idx - 1) hbound (by omega)]
            exact hp2
          · by_cases hhigh : pi + 1 + es.length ≤ idx
            · -- past the payload: the splice changed nothing at all
              have hun := appendFrom_above_unchanged es (w.nodes i).log (pi + 1) idx hbound
                (by omega) hhigh (by rw [hget]; rfl)
              rw [hun idx] at hget
              obtain ⟨p, hp1, hp2⟩ := h.logs i idx e hget hidx
              refine ⟨p, chain_mono hp1, ?_⟩
              unfold LogStore.termAt at hp2 ⊢
              rw [hun (idx - 1)]
              exact hp2
            · -- inside the payload: the entry is the payload's, by uniqueness
              have hn : idx - (pi + 1) < es.length := by omega
              obtain ⟨en, hen⟩ : ∃ en, es[idx - (pi + 1)]? = some en :=
                ⟨es[idx - (pi + 1)], List.getElem?_eq_getElem hn⟩
              have hterm := appendFrom_termAt es (w.nodes i).log (pi + 1) (idx - (pi + 1)) en
                hbound (by omega) hen
              rw [show pi + 1 + (idx - (pi + 1)) = idx by omega] at hterm
              have heq : e = en := by
                have h1 : e.term = en.term := by
                  unfold LogStore.termAt at hterm
                  rw [hget] at hterm
                  simpa using hterm
                obtain ⟨c1, hc1⟩ := hb'.logs i idx e (by rw [act_nodes_self, hl]; exact hget)
                obtain ⟨c2, hc2⟩ := hbo.msgs src i term l pi pt es lc (idx - (pi + 1)) en
                  (hdel src (Msg.appendEntries term l pi pt es lc) rfl) hen
                rw [show pi + 1 + (idx - (pi + 1)) = idx by omega] at hc2
                exact entry_unique hnd hr' hc1 (created_mono hc2) h1
              obtain ⟨p, hp1, hp2⟩ := h.msgs src i term l pi pt es lc (idx - (pi + 1)) en
                (hdel src (Msg.appendEntries term l pi pt es lc) rfl) hen
                (by omega)
              rw [show pi + 1 + (idx - (pi + 1)) = idx by omega] at hp1
              refine ⟨p, chain_mono (heq ▸ hp1), ?_⟩
              by_cases hz : idx - (pi + 1) = 0
              · -- first payload entry: its predecessor is the index the check matched
                rw [if_pos hz] at hp2
                have hpi1 : pi ≠ 0 := by omega
                have hcheck : LogStore.termAt (w.nodes i).log pi = some p := by
                  rw [hp2]; exact hchk hpi1
                unfold LogStore.termAt at hcheck ⊢
                rw [appendFrom_get_of_lt es _ (pi + 1) (idx - 1) hbound (by omega)]
                rw [show idx - 1 = pi by omega]
                exact hcheck
              · rw [if_neg hz] at hp2
                obtain ⟨e', he', hpe⟩ := hp2
                have := appendFrom_termAt es (w.nodes i).log (pi + 1)
                  (idx - (pi + 1) - 1) e' hbound (by omega) he'
                rw [show pi + 1 + (idx - (pi + 1) - 1) = idx - 1 by omega] at this
                rw [this, hpe]
      · rw [act_nodes_ne _ _ _ hij] at hget ⊢
        obtain ⟨p, hp1, hp2⟩ := h.logs i idx e hget hidx
        exact ⟨p, chain_mono hp1, hp2⟩
    have hcr : ChainCreated (w.act j ev) := by
      intro idx e p hmem
      rw [act_chain] at hmem
      rw [act_created]
      rcases List.mem_append.mp hmem with h' | h'
      · obtain ⟨c, hc⟩ := h.created idx e p h'
        exact ⟨c, List.mem_append_left _ hc⟩
      · obtain ⟨hlead, hidx0, hterm0, rid, cmd, hev⟩ := mem_chainOf h'
        refine ⟨j, List.mem_append_right _ ?_⟩
        subst hev
        unfold chainOf at h'
        dsimp only at h'
        rw [if_pos hlead] at h'
        simp only [List.mem_singleton, Prod.mk.injEq] at h'
        unfold createdOf
        dsimp only
        rw [if_pos hlead]
        refine List.mem_singleton.mpr ?_
        rw [h'.1, h'.2.1]
    have hdt : ChainDet (w.act j ev) := by
      have hl := ledInv_reachable hnd hr
      have hc0 := cInv_reachable hnd hr
      -- a fresh link sits beyond everything its creator already holds
      have collide : ∀ idx e p p', (idx, e, p) ∈ w.chain →
          (idx, e, p') ∈ chainOf j (Protocol.step (w.nodes j) ev).1 ev → p = p' := by
        intro idx e p p' hold hnew
        exfalso
        obtain ⟨hlead, hidx0, hterm0, rid, cmd, hev⟩ := mem_chainOf hnew
        obtain ⟨c, hc⟩ := h.created idx e p hold
        have hpre : (w.nodes j).role = Role.leader := by
          subst hev
          rcases Classical.em ((w.nodes j).role = Role.leader) with hq | hq
          · exact hq
          · exfalso
            rw [Protocol.step, handleClientReq, if_pos (by simp [hq])] at hlead
            exact hq hlead
        have hterm1 : (Protocol.step (w.nodes j) (Event.clientReq rid cmd)).1.currentTerm
            = (w.nodes j).currentTerm := by rw [Protocol.step, handleClientReq_term_eq]
        have hledx : (c, e.term) ∈ w.led := hc0.ledRec c idx e hc
        have hledj : (j, e.term) ∈ w.led := by
          rw [hterm0]
          subst hev
          rw [hterm1]
          exact hl.cur j hpre
        have hcj : c = j := led_unique hnd hr hledx hledj
        subst hcj
        have hold' : (w.nodes c).currentTerm = e.term := by
          rw [hterm0]; subst hev; rw [hterm1]
        have hget := hc0.inLeader c idx e hc hold'
        have hle := ((LogStore.get_isSome_iff (w.nodes c).log idx).mp (by rw [hget]; rfl)).2
        subst hev
        rw [Protocol.step, handleClientReq_log hpre, LogStore.lastIndex_append] at hidx0
        omega
      intro idx e p₁ p₂ hm₁ hm₂
      rw [act_chain] at hm₁ hm₂
      rcases List.mem_append.mp hm₁ with h₁ | h₁ <;>
        rcases List.mem_append.mp hm₂ with h₂ | h₂
      · exact h.det idx e p₁ p₂ h₁ h₂
      · exact collide idx e p₁ p₂ h₁ h₂
      · exact (collide idx e p₂ p₁ h₂ h₁).symm
      · obtain ⟨_, _, _, rid, cmd, hev⟩ := mem_chainOf h₁
        subst hev
        unfold chainOf at h₁ h₂
        dsimp only at h₁ h₂
        by_cases hq : (Protocol.step (w.nodes j) (Event.clientReq rid cmd)).1.role = Role.leader
        · rw [if_pos hq] at h₁ h₂
          simp only [List.mem_singleton, Prod.mk.injEq] at h₁ h₂
          rw [h₁.2.2, h₂.2.2]
        · rw [if_neg hq] at h₁; simp at h₁
    refine ⟨hlogs, ?_, hcr, hdt⟩
    intro src dst t l pi pt es lc n e hp hn hidx
    rw [act_sent] at hp
    rcases List.mem_append.mp hp with hp' | hp'
    · obtain ⟨p, hp1, hp2⟩ := h.msgs src dst t l pi pt es lc n e hp' hn hidx
      exact ⟨p, chain_mono hp1, hp2⟩
    · rcases mem_sendsOf hp' with ⟨to, m, heq, hact⟩
      have hsj : src = j := congrArg (fun q => q.1) heq
      have hm : m = Msg.appendEntries t l pi pt es lc := by
        have := congrArg (fun q => q.2.2) heq; simpa using this.symm
      subst hm; subst hsj
      obtain ⟨p0, hp0⟩ := step_appendEntries_payload hact
      simp only [appendEntriesTo] at hp0
      obtain ⟨htt, hll, hpi, hpt, hes, hlc⟩ := Msg.appendEntries.inj hp0
      have hni : max 1 (PeerMap.get (Protocol.step (w.nodes src) ev).1.nextIndex p0
          (LogStore.lastIndex (Protocol.step (w.nodes src) ev).1.log + 1)) = pi + 1 := by
        rw [hpi]; have := Nat.le_max_left 1
          (PeerMap.get (Protocol.step (w.nodes src) ev).1.nextIndex p0
            (LogStore.lastIndex (Protocol.step (w.nodes src) ev).1.log + 1))
        omega
      have hpay : ∀ m' (e' : Entry), es[m']? = some e' →
          LogStore.get (Protocol.step (w.nodes src) ev).1.log (pi + 1 + m') = some e' := by
        intro m' e' hm'
        rw [hes] at hm'
        have := appendEntriesTo_entries (s := (Protocol.step (w.nodes src) ev).1) (p := p0) hm'
        rwa [hni] at this
      obtain ⟨p, hp1, hp2⟩ := hlogs src (pi + 1 + n) e
        (by rw [act_nodes_self]; exact hpay n e hn) hidx
      rw [act_nodes_self] at hp2
      refine ⟨p, hp1, ?_⟩
      by_cases hz : n = 0
      · rw [if_pos hz]
        subst hz
        rw [show pi + 1 + 0 - 1 = pi by omega] at hp2
        rw [hpt, show max 1 (PeerMap.get (Protocol.step (w.nodes src) ev).1.nextIndex p0
              (LogStore.lastIndex (Protocol.step (w.nodes src) ev).1.log + 1)) - 1 = pi by
            rw [hni]; omega, hp2]
        simp
      · rw [if_neg hz]
        have hn' : n < es.length := by
          rcases Nat.lt_or_ge n es.length with hc | hc
          · exact hc
          · exfalso; rw [List.getElem?_eq_none hc] at hn; exact absurd hn (by simp)
        obtain ⟨e', he'⟩ : ∃ e', es[n - 1]? = some e' :=
          ⟨es[n - 1], List.getElem?_eq_getElem (by omega)⟩
        refine ⟨e', he', ?_⟩
        unfold LogStore.termAt at hp2
        rw [show pi + 1 + n - 1 = pi + 1 + (n - 1) by omega, hpay (n - 1) e' he'] at hp2
        simpa using hp2.symm
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
      -- logs are durable; the chain, the payloads and the mint records do not move
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i idx e hget h2
        rw [crash_chain]
        by_cases hij : i = k
        · subst hij
          rw [crash_nodes_self, restart_log] at hget ⊢
          exact h.logs i idx e hget h2
        · rw [crash_nodes_ne _ _ hij] at hget ⊢; exact h.logs i idx e hget h2
      · intro src dst t l pi pt es lc n e hp hn h2
        rw [crash_sent] at hp; rw [crash_chain]
        exact h.msgs src dst t l pi pt es lc n e hp hn h2
      · intro idx e p hm; rw [crash_chain] at hm; rw [crash_created]
        exact h.created idx e p hm
      · intro idx e p₁ p₂ h₁ h₂
        rw [crash_chain] at h₁ h₂; exact h.det idx e p₁ p₂ h₁ h₂

/-- The chain invariants hold in every reachable world. -/
theorem chInv_reachable {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) : ChInv members w := by
  induction h with
  | init => exact chInv_init members
  | tail hr hs ih => exact chInv_step hnd hr ih hs

/--
**Two logs agreeing at an index agree at the index below it.**

The single downward step of the Log Matching argument: the shared entry pins
down a single recorded predecessor term, and a term at an index pins down the
entry there.
-/
theorem log_agree_pred {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) {i j idx : Nat} {e : Entry}
    (h₁ : LogStore.get (w.nodes i).log idx = some e)
    (h₂ : LogStore.get (w.nodes j).log idx = some e)
    (hidx : 2 ≤ idx) :
    LogStore.get (w.nodes i).log (idx - 1) = LogStore.get (w.nodes j).log (idx - 1) := by
  have hch := chInv_reachable hnd hrch
  obtain ⟨p₁, hm₁, ht₁⟩ := hch.logs i idx e h₁ hidx
  obtain ⟨p₂, hm₂, ht₂⟩ := hch.logs j idx e h₂ hidx
  -- both logs record the same predecessor term
  obtain ⟨v₁, hv₁⟩ : ∃ v, LogStore.get (w.nodes i).log (idx - 1) = some v := by
    unfold LogStore.termAt at ht₁
    cases hq : LogStore.get (w.nodes i).log (idx - 1) with
    | none => rw [hq] at ht₁; simp at ht₁
    | some v => exact ⟨v, rfl⟩
  obtain ⟨v₂, hv₂⟩ : ∃ v, LogStore.get (w.nodes j).log (idx - 1) = some v := by
    unfold LogStore.termAt at ht₂
    cases hq : LogStore.get (w.nodes j).log (idx - 1) with
    | none => rw [hq] at ht₂; simp at ht₂
    | some v => exact ⟨v, rfl⟩
  have hchain : p₁ = p₂ := by
    obtain ⟨c₁, hc₁⟩ := (bInv_reachable hrch).logs i idx e h₁
    obtain ⟨c₂, hc₂⟩ := (bInv_reachable hrch).logs j idx e h₂
    exact (chInv_reachable hnd hrch).det idx e p₁ p₂ hm₁ hm₂
  have hterm : v₁.term = v₂.term := by
    unfold LogStore.termAt at ht₁ ht₂
    rw [hv₁] at ht₁; rw [hv₂] at ht₂
    have e₁ : v₁.term = p₁ := by simpa using ht₁
    have e₂ : v₂.term = p₂ := by simpa using ht₂
    rw [e₁, e₂, hchain]
  rw [hv₁, hv₂, log_entry_unique hnd hrch hv₁ hv₂ hterm]

/--
**Log Matching, part two.**

If two replicas hold the same entry at index `idx`, their logs are *identical*
at every index up to `idx`.

Proved by chasing predecessor links downwards: the shared entry determines one
recorded predecessor term, and a term at an index determines the entry there
(`log_entry_unique`), so agreement propagates one index at a time to the start.
-/
theorem log_agree_below {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) {i j : Nat} :
    ∀ (d idx : Nat) (e : Entry), idx ≤ d →
      LogStore.get (w.nodes i).log idx = some e →
      LogStore.get (w.nodes j).log idx = some e →
      ∀ k, k ≤ idx → LogStore.get (w.nodes i).log k = LogStore.get (w.nodes j).log k := by
  intro d
  induction d with
  | zero =>
      intro idx e hd h₁ h₂ k hk
      -- `idx = 0` holds no entry
      exact absurd h₁ (by rw [show idx = 0 by omega]; simp)
  | succ n ih =>
      intro idx e hd h₁ h₂ k hk
      by_cases hk0 : k = idx
      · subst hk0; rw [h₁, h₂]
      · -- step down one index and recurse
        by_cases hidx1 : idx ≤ 1
        · -- then `k = 0`, where every log reads `none`
          have hk00 : k = 0 := by omega
          subst hk00
          simp
        have hidx2 : 2 ≤ idx := by omega
        have hpred := log_agree_pred hnd hrch h₁ h₂ hidx2
        obtain ⟨v, hv⟩ : ∃ v, LogStore.get (w.nodes i).log (idx - 1) = some v := by
          cases hq : LogStore.get (w.nodes i).log (idx - 1) with
          | none =>
              exfalso
              have := get_isSome_below h₁ (m := idx - 1) (by omega) (by omega)
              rw [hq] at this; exact Bool.noConfusion this
          | some v => exact ⟨v, rfl⟩
        exact ih (idx - 1) v (by omega) hv (by rw [← hpred]; exact hv) k (by omega)

/-- The headline form: `RaftKV.Protocol.LogMatching` holds in every reachable world. -/
theorem logMatching {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) : LogMatching w := by
  intro i j idx e₁ e₂ h₁ h₂ hterm k hk
  have he : e₁ = e₂ := log_entry_unique hnd hrch h₁ h₂ hterm
  subst he
  exact log_agree_below hnd hrch idx idx e₁ (Nat.le_refl _) h₁ h₂ k hk

end RaftKV.Proof
