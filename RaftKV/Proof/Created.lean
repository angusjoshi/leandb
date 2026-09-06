import RaftKV.Proof.Led

/-!
# Entries are uniquely determined by index and term

`World.created` is proof-only ghost state recording every entry a leader has
minted for a client, tagged with its creator and index.

The theorem below — **no two distinct entries are ever created at the same index
in the same term** — is the substance of Raft's Log Matching Property, part one.
Everything the paper says about logs agreeing rests on it.

The argument is short now that the groundwork is in place:

* a creator of a term-`t` entry is recorded in `led` for term `t`, and
  `led_unique` says there is only ever one such node;
* that node's log still holds every term-`t` entry it created for as long as its
  term is `t` (`CreatedInLeader`), because `leader_stable` keeps it in office and
  `leader_log_monotone` stops its log being rewritten;
* a leader mints at index `lastIndex + 1`, which is beyond everything its log
  currently holds — so it can never collide with one of its own earlier entries.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [LawfulLogStore σ] [KVStore κ]

theorem act_created (w : World σ κ) (j : Nat) (ev : Event) :
    (w.act j ev).created = w.created ++ createdOf j (Protocol.step (w.nodes j) ev).1 ev := rfl

theorem mem_createdOf {i j k : Nat} {e : Entry} {s : NodeState σ κ} {ev : Event}
    (h : (i, k, e) ∈ createdOf j s ev) :
    i = j ∧ s.role = Role.leader ∧ k = LogStore.lastIndex s.log ∧ e.term = s.currentTerm := by
  unfold createdOf at h
  cases ev with
  | clientReq rid cmd =>
      dsimp only at h
      split at h
      · rename_i hr
        simp only [List.mem_singleton, Prod.mk.injEq] at h
        exact ⟨h.1, hr, h.2.1, by rw [h.2.2]⟩
      · simp at h
  | recv a b => simp at h
  | electionTimeout => simp at h
  | heartbeatTimeout => simp at h

/--
Everything a freshly minted entry tells us, as a standalone fact: who minted it,
that they were leading, at which index, and that their log now holds it there.
-/
theorem createdOf_get {j c k : Nat} {e : Entry} {ev : Event} {pre : NodeState σ κ}
    (h : (c, k, e) ∈ createdOf j (Protocol.step pre ev).1 ev) :
    c = j ∧ (Protocol.step pre ev).1.role = Role.leader
      ∧ e.term = (Protocol.step pre ev).1.currentTerm
      ∧ k = LogStore.lastIndex (Protocol.step pre ev).1.log
      ∧ LogStore.get (Protocol.step pre ev).1.log k = some e := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_createdOf h
  refine ⟨h1, h2, h4, h3, ?_⟩
  cases ev with
  | recv a b => simp [createdOf] at h
  | electionTimeout => simp [createdOf] at h
  | heartbeatTimeout => simp [createdOf] at h
  | clientReq rid cmd =>
      have hlead : pre.role = Role.leader := by
        rcases Classical.em (pre.role = Role.leader) with hc | hc
        · exact hc
        · exfalso
          rw [Protocol.step, handleClientReq, if_pos (by simp [hc])] at h2
          exact hc h2
      have hlog : (Protocol.step pre (Event.clientReq rid cmd)).1.log
          = LogStore.append pre.log { term := pre.currentTerm, cmd := cmd, reqId := rid } := by
        rw [Protocol.step]; exact handleClientReq_log hlead
      have hterm : (Protocol.step pre (Event.clientReq rid cmd)).1.currentTerm
          = pre.currentTerm := by rw [Protocol.step]; exact handleClientReq_term_eq
      have hek : e = { term := pre.currentTerm, cmd := cmd, reqId := rid } := by
        unfold createdOf at h
        dsimp only at h
        rw [if_pos h2] at h
        simp only [List.mem_singleton, Prod.mk.injEq] at h
        rw [h.2.2, hterm]
      rw [h3, hlog, LogStore.lastIndex_append, hek]
      exact LogStore.get_append_self _ _

/-- Every created entry's creator is on record as having led its term. -/
def CreatedLed (w : World σ κ) : Prop :=
  ∀ i k e, (i, k, e) ∈ w.created → (i, e.term) ∈ w.led

/-- A creator's log still holds what it created, for as long as its term stands. -/
def CreatedInLeader (w : World σ κ) : Prop :=
  ∀ i k e, (i, k, e) ∈ w.created → (w.nodes i).currentTerm = e.term →
    LogStore.get (w.nodes i).log k = some e

/-- **No two distinct entries are ever created at the same index in the same term.** -/
def CreatedUnique (w : World σ κ) : Prop :=
  ∀ i j k e₁ e₂, (i, k, e₁) ∈ w.created → (j, k, e₂) ∈ w.created →
    e₁.term = e₂.term → e₁ = e₂

/-- The created-entry invariants. -/
structure CInv (members : List Nat) (w : World σ κ) : Prop where
  /-- Creators led their term. -/
  ledRec : CreatedLed w
  /-- Creators retain what they made. -/
  inLeader : CreatedInLeader w
  /-- Index and term determine the entry. -/
  uniq : CreatedUnique w

theorem cInv_init (members : List Nat) :
    CInv (σ := σ) (κ := κ) members (World.init members) where
  ledRec := by intro i k e h; simp [World.init] at h
  inLeader := by intro i k e h; simp [World.init] at h
  uniq := by intro i j k e₁ e₂ h; simp [World.init] at h

/-- **The created-entry invariants are preserved by every step.** -/
theorem cInv_step {members : List Nat} {w w' : World σ κ}
    (hnd : members.Nodup) (hr : Reachable members w)
    (h : CInv members w) (hs : Step members w w') : CInv members w' := by
  have hl := ledInv_reachable hnd hr
  have key : ∀ (j : Nat) (ev : Event), w' = w.act j ev → CInv members w' := by
    intro j ev hw
    subst hw
    -- Everything we need to know about a freshly minted entry.
    have fresh : ∀ i k e, (i, k, e) ∈ createdOf j (Protocol.step (w.nodes j) ev).1 ev →
        i = j ∧ (w.nodes j).role = Role.leader ∧ e.term = (w.nodes j).currentTerm
          ∧ k = LogStore.lastIndex (w.nodes j).log + 1
          ∧ ((w.act j ev).nodes j).log = LogStore.append (w.nodes j).log e := by
      intro i k e hmem
      cases ev with
      | recv a b => simp [createdOf] at hmem
      | electionTimeout => simp [createdOf] at hmem
      | heartbeatTimeout => simp [createdOf] at hmem
      | clientReq rid cmd =>
          obtain ⟨h1, h2, h3, h4⟩ := mem_createdOf hmem
          have hlead : (w.nodes j).role = Role.leader := by
            rcases Classical.em ((w.nodes j).role = Role.leader) with hc | hc
            · exact hc
            · exfalso
              rw [Protocol.step, handleClientReq, if_pos (by simp [hc])] at h2
              exact hc h2
          have hlog : (Protocol.step (w.nodes j) (Event.clientReq rid cmd)).1.log
              = LogStore.append (w.nodes j).log
                  { term := (w.nodes j).currentTerm, cmd := cmd, reqId := rid } := by
            rw [Protocol.step]; exact handleClientReq_log hlead
          have hterm : (Protocol.step (w.nodes j) (Event.clientReq rid cmd)).1.currentTerm
              = (w.nodes j).currentTerm := by
            rw [Protocol.step]; exact handleClientReq_term_eq
          have hek : e = { term := (w.nodes j).currentTerm, cmd := cmd, reqId := rid } := by
            unfold createdOf at hmem
            dsimp only at hmem
            rw [if_pos h2] at hmem
            simp only [List.mem_singleton, Prod.mk.injEq] at hmem
            rw [hmem.2.2, hterm]
          refine ⟨h1, hlead, by rw [hek], ?_, ?_⟩
          · rw [h3, hlog, LogStore.lastIndex_append]
          · rw [act_nodes_self, hlog, hek]
    -- A fresh entry's creator is a leader in the post-state too.
    have freshPost : ∀ i k e, (i, k, e) ∈ createdOf j (Protocol.step (w.nodes j) ev).1 ev →
        (Protocol.step (w.nodes j) ev).1.role = Role.leader
          ∧ (Protocol.step (w.nodes j) ev).1.currentTerm = e.term := by
      intro i k e hmem
      obtain ⟨_, hlead, hterm, _, _⟩ := fresh i k e hmem
      cases ev with
      | recv a b => simp [createdOf] at hmem
      | electionTimeout => simp [createdOf] at hmem
      | heartbeatTimeout => simp [createdOf] at hmem
      | clientReq rid cmd =>
          refine ⟨?_, by rw [Protocol.step, handleClientReq_term_eq, hterm]⟩
          rw [Protocol.step, handleClientReq, if_neg (by rw [hlead]; simp)]
          dsimp only; simp [hlead]
    refine ⟨?_, ?_, ?_⟩
    · -- CreatedLed
      intro i k e hmem
      rw [act_created] at hmem
      rw [act_led]
      rcases List.mem_append.mp hmem with h' | h'
      · exact List.mem_append_left _ (h.ledRec i k e h')
      · obtain ⟨h1, _, _, _, _⟩ := fresh i k e h'
        obtain ⟨hlead, hterm⟩ := freshPost i k e h'
        subst h1
        refine List.mem_append_right _ ?_
        rw [← hterm]
        exact ledOf_self hlead
    · -- CreatedInLeader
      intro i k e hmem hterm
      rw [act_created] at hmem
      rcases List.mem_append.mp hmem with h' | h'
      · by_cases hij : i = j
        · subst hij
          rw [act_nodes_self] at hterm ⊢
          have hled : (i, e.term) ∈ w.led := h.ledRec i k e h'
          have hb := hl.bound i e.term hled
          have hmono := act_term_mono w i ev i
          rw [act_nodes_self] at hmono
          have hold : (w.nodes i).currentTerm = e.term :=
            Nat.le_antisymm (by rw [← hterm]; exact hmono) hb
          have hget := h.inLeader i k e h' hold
          rcases led_log_stable hnd hr hs hled hold (by rw [act_nodes_self]; exact hterm)
            with hlog | ⟨e', hlog⟩
          · rw [act_nodes_self] at hlog; rw [hlog]; exact hget
          · rw [act_nodes_self] at hlog
            rw [hlog]
            refine (LogStore.get_append_of_le _ _ _ ?_).trans hget
            exact ((LogStore.get_isSome_iff (w.nodes i).log k).mp (by rw [hget]; rfl)).2
        · rw [act_nodes_ne _ _ _ hij] at hterm ⊢
          exact h.inLeader i k e h' hterm
      · obtain ⟨h1, _, _, h4, h5⟩ := fresh i k e h'
        subst h1
        rw [h5, h4]
        exact LogStore.get_append_self _ _
    · -- CreatedUnique
      intro i j' k e₁ e₂ hm₁ hm₂ hteq
      rw [act_created] at hm₁ hm₂
      -- A fresh entry lands strictly beyond everything its creator already holds,
      -- so it cannot collide with anything created earlier in the same term.
      have collide : ∀ a b (x y : Entry), (a, k, x) ∈ w.created →
          (b, k, y) ∈ createdOf j (Protocol.step (w.nodes j) ev).1 ev →
          x.term = y.term → x = y := by
        intro a b x y hx hy hxy
        exfalso
        obtain ⟨hb, hlead, hyterm, hk, _⟩ := fresh b k y hy
        have hledx : (a, x.term) ∈ w.led := h.ledRec a k x hx
        have hledy : (j, y.term) ∈ w.led := by
          rw [hyterm]; exact hl.cur j hlead
        have haj : a = j := led_unique hnd hr hledx (hxy ▸ hledy)
        subst haj
        have hold : (w.nodes a).currentTerm = x.term := by rw [hxy, hyterm]
        have hget := h.inLeader a k x hx hold
        have hle := ((LogStore.get_isSome_iff (w.nodes a).log k).mp (by rw [hget]; rfl)).2
        omega
      rcases List.mem_append.mp hm₁ with h₁ | h₁ <;>
        rcases List.mem_append.mp hm₂ with h₂ | h₂
      · exact h.uniq i j' k e₁ e₂ h₁ h₂ hteq
      · exact collide i j' e₁ e₂ h₁ h₂ hteq
      · exact (collide j' i e₂ e₁ h₂ h₁ hteq.symm).symm
      · cases ev with
        | recv a b => simp [createdOf] at h₁
        | electionTimeout => simp [createdOf] at h₁
        | heartbeatTimeout => simp [createdOf] at h₁
        | clientReq rid cmd =>
            unfold createdOf at h₁ h₂
            dsimp only at h₁ h₂
            by_cases hc :
                (Protocol.step (w.nodes j) (Event.clientReq rid cmd)).1.role = Role.leader
            · rw [if_pos hc] at h₁ h₂
              simp only [List.mem_singleton, Prod.mk.injEq] at h₁ h₂
              rw [h₁.2.2, h₂.2.2]
            · rw [if_neg hc] at h₁; simp at h₁
  cases hs with
  | deliver s d m hd hm => exact key d _ rfl
  | electionTimeout k hk => exact key k _ rfl
  | heartbeat k hk => exact key k _ rfl
  | client k rid cmd hk => exact key k _ rfl
  | crash k hk =>
      -- nothing is created, and the log a creator holds is durable
      refine ⟨?_, ?_, ?_⟩
      · intro i k' e hm; rw [crash_created] at hm; rw [crash_led]; exact h.ledRec i k' e hm
      · intro i k' e hm hterm
        rw [crash_created] at hm
        by_cases hij : i = k
        · subst hij
          rw [crash_nodes_self, restart_log]
          rw [crash_nodes_self, restart_currentTerm] at hterm
          exact h.inLeader i k' e hm hterm
        · rw [crash_nodes_ne _ _ hij] at hterm ⊢; exact h.inLeader i k' e hm hterm
      · intro i j' k' e₁ e₂ h₁ h₂ hteq
        rw [crash_created] at h₁ h₂; exact h.uniq i j' k' e₁ e₂ h₁ h₂ hteq

/-- The created-entry invariants hold in every reachable world. -/
theorem cInv_reachable {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) : CInv members w := by
  induction h with
  | init => exact cInv_init members
  | tail hr hs ih => exact cInv_step hnd hr ih hs

/--
**Index and term determine an entry.**

In any reachable world, two entries minted at the same log index in the same
term are the same entry. This is Raft's Log Matching Property, part one.
-/
theorem entry_unique {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) {i j k : Nat} {e₁ e₂ : Entry}
    (h₁ : (i, k, e₁) ∈ w.created) (h₂ : (j, k, e₂) ∈ w.created)
    (hterm : e₁.term = e₂.term) : e₁ = e₂ :=
  (cInv_reachable hnd hrch).uniq i j k e₁ e₂ h₁ h₂ hterm

end RaftKV.Proof
