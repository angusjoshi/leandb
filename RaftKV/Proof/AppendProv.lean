import RaftKV.Proof.Winner
import RaftKV.Proof.LogOps

/-!
# Provenance of `appendEntries`

Where replication traffic comes from. Two facts:

* `step_appendEntries_leader` — a node only ever transmits `appendEntries` while
  it is a leader, stamped with its own term and its own id; and
* `AEFromWinner` — consequently, every `appendEntries` for term `t` anywhere on
  the wire was sent by **the** winner of term `t`.

Together with `PacketsNotSelf` this rules out the one remaining way a leader
could lose leadership without advancing its term: receiving `appendEntries` for
its own term. No such message can exist unless the leader sent it to itself,
which it never does.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [KVStore κ]

/-- Any `appendEntries` in a broadcast carries the sender's current term. -/
theorem broadcastAppend_term {s : NodeState σ κ} {to t l pi pt : Nat}
    {es : List Entry} {lc : Nat}
    (h : Action.send to (Msg.appendEntries t l pi pt es lc) ∈ broadcastAppend s) :
    t = s.currentTerm := by
  rw [broadcastAppend] at h
  rcases List.mem_map.mp h with ⟨p, _, heq⟩
  have hm := (Action.send.inj heq).2
  simp only [appendEntriesTo] at hm
  exact ((Msg.appendEntries.inj hm).1).symm

/--
**`appendEntries` is only ever transmitted by a leader, stamped with its own
term.**

Every emission site is guarded by leadership: `becomeLeader`'s initial
assertion of authority, the heartbeat, a client append, and the back-off retry
in `handleAppendEntriesResp`.
-/
theorem step_appendEntries_leader {s : NodeState σ κ} {ev : Event}
    {to t l pi pt : Nat} {es : List Entry} {lc : Nat}
    (h : Action.send to (Msg.appendEntries t l pi pt es lc) ∈ (Protocol.step s ev).2) :
    (Protocol.step s ev).1.role = Role.leader ∧ (Protocol.step s ev).1.currentTerm = t := by
  cases ev with
  | recv src m =>
      cases m with
      | requestVote a b c d =>
          rw [Protocol.step] at h
          rcases handleRequestVote_send_shape h with ⟨_, _, heq⟩
          exact absurd heq (by simp)
      | appendEntries a b c d e f =>
          rw [Protocol.step] at h
          rcases handleAppendEntries_send_shape h with ⟨_, _, _, heq⟩
          exact absurd heq (by simp)
      | requestVoteResp term g =>
          rw [Protocol.step, handleRequestVoteResp] at h ⊢
          by_cases hgt : term > s.currentTerm
          · rw [if_pos hgt] at h; exact absurd h stepDown_no_send
          · rw [if_neg hgt] at h ⊢
            by_cases hguard : s.role != Role.candidate || term != s.currentTerm || !g
            · rw [if_pos hguard] at h; simp at h
            · rw [if_neg hguard] at h ⊢
              dsimp only at h ⊢
              by_cases hmem : s.votesGranted.contains src = true
              · rw [if_pos hmem] at h ⊢
                by_cases hmaj : s.cfg.isMajority s.votesGranted = true
                · rw [if_pos hmaj] at h ⊢
                  rw [becomeLeader] at h
                  exact ⟨rfl, (broadcastAppend_term h).symm⟩
                · rw [if_neg hmaj] at h; simp at h
              · rw [if_neg hmem] at h ⊢
                by_cases hmaj : s.cfg.isMajority (src :: s.votesGranted) = true
                · rw [if_pos hmaj] at h ⊢
                  rw [becomeLeader] at h
                  exact ⟨rfl, (broadcastAppend_term h).symm⟩
                · rw [if_neg hmaj] at h; simp at h
      | appendEntriesResp term ok mi =>
          rw [Protocol.step, handleAppendEntriesResp] at h ⊢
          by_cases hgt : term > s.currentTerm
          · rw [if_pos hgt] at h; exact absurd h stepDown_no_send
          · rw [if_neg hgt] at h ⊢
            by_cases hguard : s.role != Role.leader || term != s.currentTerm
            · rw [if_pos hguard] at h; simp at h
            · rw [if_neg hguard] at h ⊢
              simp only [Bool.not_eq_true, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hguard
              by_cases hok : ok = true
              · rw [if_pos hok] at h; exact absurd h applyCommitted_no_send
              · rw [if_neg hok] at h ⊢
                dsimp only at h ⊢
                have heq := List.mem_singleton.mp h
                have hm := (Action.send.inj heq).2
                simp only [appendEntriesTo] at hm
                exact ⟨by simpa using hguard.1, ((Msg.appendEntries.inj hm).1).symm⟩
  | clientReq rid cmd =>
      rw [Protocol.step, handleClientReq] at h ⊢
      by_cases hguard : s.role != Role.leader
      · rw [if_pos hguard] at h; simp at h
      · rw [if_neg hguard] at h ⊢
        simp only [bne_eq_false_iff_eq, Bool.not_eq_true] at hguard
        dsimp only at h ⊢
        rcases List.mem_append.mp h with h' | h'
        · exact ⟨by simpa using hguard, (broadcastAppend_term h').symm⟩
        · exact absurd h' applyCommitted_no_send
  | electionTimeout =>
      rw [Protocol.step] at h ⊢
      by_cases hlead : s.role == Role.leader
      · rw [if_pos hlead] at h; simp at h
      · rw [if_neg hlead] at h ⊢
        rw [startElection] at h ⊢
        dsimp only at h ⊢
        by_cases hmaj : s.cfg.isMajority [s.cfg.me] = true
        · rw [if_pos hmaj] at h ⊢
          rw [becomeLeader] at h
          exact ⟨rfl, (broadcastAppend_term h).symm⟩
        · rw [if_neg hmaj] at h
          rcases List.mem_map.mp h with ⟨p, _, heq⟩
          exact absurd (Action.send.inj heq).2 (by simp)
  | heartbeatTimeout =>
      rw [Protocol.step] at h ⊢
      by_cases hlead : s.role == Role.leader
      · rw [if_pos hlead] at h ⊢
        exact ⟨by simpa using hlead, (broadcastAppend_term h).symm⟩
      · rw [if_neg hlead] at h; simp at h

/-- A broadcast entry is literally `appendEntriesTo` of the sender's state. -/
theorem broadcastAppend_mem {s : NodeState σ κ} {to : Nat} {m : Msg}
    (h : Action.send to m ∈ broadcastAppend s) : m = appendEntriesTo s to := by
  rw [broadcastAppend] at h
  rcases List.mem_map.mp h with ⟨p, _, heq⟩
  have h1 := (Action.send.inj heq).1
  have h2 := (Action.send.inj heq).2
  subst h1; exact h2.symm

/--
**Every `appendEntries` a node emits is `appendEntriesTo` of its own post-state.**

Consequently its payload is a tail of the sender's log at the moment of sending,
which is what lets `LogFromCreated` be carried from logs onto the wire.
-/
theorem step_appendEntries_payload {s : NodeState σ κ} {ev : Event}
    {to t l pi pt : Nat} {es : List Entry} {lc : Nat}
    (h : Action.send to (Msg.appendEntries t l pi pt es lc) ∈ (Protocol.step s ev).2) :
    ∃ p, Msg.appendEntries t l pi pt es lc = appendEntriesTo (Protocol.step s ev).1 p := by
  cases ev with
  | recv src m =>
      cases m with
      | requestVote a b c d =>
          rw [Protocol.step] at h
          rcases handleRequestVote_send_shape h with ⟨_, _, heq⟩
          exact absurd heq (by simp)
      | appendEntries a b c d e f =>
          rw [Protocol.step] at h
          rcases handleAppendEntries_send_shape h with ⟨_, _, _, heq⟩
          exact absurd heq (by simp)
      | requestVoteResp term g =>
          rw [Protocol.step, handleRequestVoteResp] at h ⊢
          by_cases hgt : term > s.currentTerm
          · rw [if_pos hgt] at h; exact absurd h stepDown_no_send
          · rw [if_neg hgt] at h ⊢
            by_cases hguard : s.role != Role.candidate || term != s.currentTerm || !g
            · rw [if_pos hguard] at h; simp at h
            · rw [if_neg hguard] at h ⊢
              dsimp only at h ⊢
              by_cases hmem : s.votesGranted.contains src = true
              · rw [if_pos hmem] at h ⊢
                by_cases hmaj : s.cfg.isMajority s.votesGranted = true
                · rw [if_pos hmaj] at h ⊢
                  rw [becomeLeader] at h
                  exact ⟨to, broadcastAppend_mem h⟩
                · rw [if_neg hmaj] at h; simp at h
              · rw [if_neg hmem] at h ⊢
                by_cases hmaj : s.cfg.isMajority (src :: s.votesGranted) = true
                · rw [if_pos hmaj] at h ⊢
                  rw [becomeLeader] at h
                  exact ⟨to, broadcastAppend_mem h⟩
                · rw [if_neg hmaj] at h; simp at h
      | appendEntriesResp term ok mi =>
          rw [Protocol.step, handleAppendEntriesResp] at h ⊢
          by_cases hgt : term > s.currentTerm
          · rw [if_pos hgt] at h; exact absurd h stepDown_no_send
          · rw [if_neg hgt] at h ⊢
            by_cases hguard : s.role != Role.leader || term != s.currentTerm
            · rw [if_pos hguard] at h; simp at h
            · rw [if_neg hguard] at h ⊢
              by_cases hok : ok = true
              · rw [if_pos hok] at h; exact absurd h applyCommitted_no_send
              · rw [if_neg hok] at h ⊢
                dsimp only at h ⊢
                exact ⟨src, (Action.send.inj (List.mem_singleton.mp h)).2⟩
  | clientReq rid cmd =>
      rw [Protocol.step, handleClientReq] at h ⊢
      by_cases hguard : s.role != Role.leader
      · rw [if_pos hguard] at h; simp at h
      · rw [if_neg hguard] at h ⊢
        dsimp only at h ⊢
        rcases List.mem_append.mp h with h' | h'
        · exact ⟨to, broadcastAppend_mem h'⟩
        · exact absurd h' applyCommitted_no_send
  | electionTimeout =>
      rw [Protocol.step] at h ⊢
      by_cases hlead : s.role == Role.leader
      · rw [if_pos hlead] at h; simp at h
      · rw [if_neg hlead] at h ⊢
        rw [startElection] at h ⊢
        dsimp only at h ⊢
        by_cases hmaj : s.cfg.isMajority [s.cfg.me] = true
        · rw [if_pos hmaj] at h ⊢
          rw [becomeLeader] at h
          exact ⟨to, broadcastAppend_mem h⟩
        · rw [if_neg hmaj] at h
          rcases List.mem_map.mp h with ⟨p, _, heq⟩
          exact absurd (Action.send.inj heq).2 (by simp)
  | heartbeatTimeout =>
      rw [Protocol.step] at h ⊢
      by_cases hlead : s.role == Role.leader
      · rw [if_pos hlead] at h ⊢
        exact ⟨to, broadcastAppend_mem h⟩
      · rw [if_neg hlead] at h; simp at h

/-! ## Destinations -/

theorem broadcastAppend_dest {s : NodeState σ κ} {to : Nat} {m : Msg}
    (h : Action.send to m ∈ broadcastAppend s) : to ∈ s.cfg.peers := by
  rw [broadcastAppend] at h
  rcases List.mem_map.mp h with ⟨p, hp, heq⟩
  rw [← (Action.send.inj heq).1]; exact hp

/-- Every message a node sends goes either to a peer or back to whoever just wrote to it. -/
theorem step_send_dest {s : NodeState σ κ} {ev : Event} {to : Nat} {m : Msg}
    (h : Action.send to m ∈ (Protocol.step s ev).2) :
    to ∈ s.cfg.peers ∨ ∃ src m', ev = Event.recv src m' ∧ to = src := by
  cases ev with
  | recv src m0 =>
      cases m0 with
      | requestVote a b c d =>
          right; refine ⟨src, _, rfl, ?_⟩
          rw [Protocol.step, handleRequestVote] at h
          split at h
          · exact (Action.send.inj (List.mem_singleton.mp h)).1
          · dsimp only at h
            split at h <;>
              (rcases List.mem_append.mp h with h' | h'
               · exact absurd h' maybeStepDown_no_send
               · exact (Action.send.inj (List.mem_singleton.mp h')).1)
      | requestVoteResp term g =>
          left
          rw [Protocol.step, handleRequestVoteResp] at h
          split at h
          · exact absurd h stepDown_no_send
          · split at h
            · simp at h
            · dsimp only at h
              split at h <;>
                (split at h
                 · rw [becomeLeader] at h
                   simpa using broadcastAppend_dest h
                 · simp at h)
      | appendEntries a b c d e f =>
          right; refine ⟨src, _, rfl, ?_⟩
          rw [Protocol.step, handleAppendEntries] at h
          split at h
          · exact (Action.send.inj (List.mem_singleton.mp h)).1
          · dsimp only at h
            split at h
            · rcases List.mem_append.mp h with h' | h'
              · exact absurd h' maybeStepDown_no_send
              · exact (Action.send.inj (List.mem_singleton.mp h')).1
            · dsimp only at h
              rcases List.mem_append.mp h with h' | h'
              · exact absurd h' maybeStepDown_no_send
              · rcases List.mem_cons.mp h' with h'' | h''
                · exact (Action.send.inj h'').1
                · exact absurd h'' applyCommitted_no_send
      | appendEntriesResp term ok mi =>
          right; refine ⟨src, _, rfl, ?_⟩
          rw [Protocol.step, handleAppendEntriesResp] at h
          split at h
          · exact absurd h stepDown_no_send
          · split at h
            · simp at h
            · split at h
              · exact absurd h applyCommitted_no_send
              · dsimp only at h
                exact (Action.send.inj (List.mem_singleton.mp h)).1
  | clientReq rid cmd =>
      left
      rw [Protocol.step, handleClientReq] at h
      split at h
      · simp at h
      · dsimp only at h
        rcases List.mem_append.mp h with h' | h'
        · simpa using broadcastAppend_dest h'
        · exact absurd h' applyCommitted_no_send
  | electionTimeout =>
      left
      rw [Protocol.step] at h
      split at h
      · simp at h
      · rw [startElection] at h
        dsimp only at h
        split at h
        · rw [becomeLeader] at h; simpa using broadcastAppend_dest h
        · rcases List.mem_map.mp h with ⟨p, hp, heq⟩
          rw [← (Action.send.inj heq).1]; exact hp
  | heartbeatTimeout =>
      left
      rw [Protocol.step] at h
      split at h
      · exact broadcastAppend_dest h
      · simp at h

/-! ## World-level provenance invariants -/

/-- No node ever addresses a packet to itself. -/
def PacketsNotSelf (w : World σ κ) : Prop := ∀ p ∈ w.sent, p.1 ≠ p.2.1

/-- Every `appendEntries` for term `t` was sent by the (unique) winner of term `t`. -/
def AEFromWinner (members : List Nat) (w : World σ κ) : Prop :=
  ∀ src dst t l pi pt es lc, (src, dst, Msg.appendEntries t l pi pt es lc) ∈ w.sent →
    WonTerm members w src t

/-- Provenance invariants, maintained together. -/
structure PInv (members : List Nat) (w : World σ κ) : Prop where
  /-- Packets are never self-addressed. -/
  notSelf : PacketsNotSelf w
  /-- Replication traffic comes from the term's winner. -/
  aeWinner : AEFromWinner members w

theorem pInv_init (members : List Nat) : PInv (σ := σ) (κ := κ) members (World.init members) where
  notSelf := by intro p hp; simp [World.init] at hp
  aeWinner := by intro src dst t l pi pt es lc hp; simp [World.init] at hp

/--
**The provenance invariants are preserved by every step.**

`PacketsNotSelf` is inductive precisely because a reply is only ever sent back
to the node that wrote to us, and by hypothesis that node was not us. Broadcasts
go to `Config.peers`, which excludes the sender by construction.
-/
theorem pInv_step {members : List Nat} {w w' : World σ κ}
    (hc : CfgInv members w) (h : PInv members w)
    (ha' : AllInv members w') (hs : Step members w w') : PInv members w' := by
  have main : ∀ (j : Nat) (ev : Event),
      (∀ src m', ev = Event.recv src m' → (src, j, m') ∈ w.sent) →
      AllInv members (w.act j ev) →
      PInv members (w.act j ev) := by
    intro j ev hdel ha
    constructor
    · intro p hp
      rw [act_sent] at hp
      rcases List.mem_append.mp hp with hp' | hp'
      · exact h.notSelf p hp'
      · rcases mem_sendsOf hp' with ⟨to, m, heq, hact⟩
        have h1 : p.1 = j := congrArg (fun q => q.1) heq
        have h2 : p.2.1 = to := congrArg (fun q => q.2.1) heq
        rw [h1, h2]
        rcases step_send_dest hact with hpeer | ⟨src, m', hev, hto⟩
        · rw [hc j] at hpeer
          exact fun hcon => Config.peers_ne hpeer (by rw [← hcon])
        · subst hev
          have := h.notSelf (src, j, m') (hdel src m' rfl)
          simp only at this
          rw [hto]
          exact fun hcon => this hcon.symm
    · intro src dst t l pi pt es lc hp
      rw [act_sent] at hp
      rcases List.mem_append.mp hp with hp' | hp'
      · exact wonTerm_act (h.aeWinner src dst t l pi pt es lc hp') _ _
      · rcases mem_sendsOf hp' with ⟨to, m, heq, hact⟩
        have h1 : src = j := congrArg (fun q => q.1) heq
        have hm : m = Msg.appendEntries t l pi pt es lc := by
          have := congrArg (fun q => q.2.2) heq; simpa using this.symm
        subst hm; subst h1
        obtain ⟨hrole, hterm⟩ := step_appendEntries_leader hact
        have hlead : ((w.act src ev).nodes src).role = Role.leader := by
          rw [act_nodes_self]; exact hrole
        have := wonTerm_of_leader ha.leader.votes ha.leader.quorum ha.ghost hlead
        rw [act_nodes_self, hterm] at this
        exact this
  cases hs with
  | deliver s d m hd hmem =>
      exact main d _ (by
        intro src' m' heq
        have h1 : s = src' := (Event.recv.inj heq).1
        have h2 : m = m' := (Event.recv.inj heq).2
        subst h2; subst h1; exact hmem) ha'
  | electionTimeout i _ => exact main i _ (fun _ _ hq => Event.noConfusion hq) ha'
  | heartbeat i _ => exact main i _ (fun _ _ hq => Event.noConfusion hq) ha'
  | client i rid cmd _ => exact main i _ (fun _ _ hq => Event.noConfusion hq) ha'
  | crash i _ =>
      refine ⟨?_, ?_⟩
      · intro p hp; rw [crash_sent] at hp; exact h.notSelf p hp
      · intro src dst t l pi pt es lc hp
        rw [crash_sent] at hp
        obtain ⟨V, h1, h2, h3, h4⟩ := h.aeWinner src dst t l pi pt es lc hp
        exact ⟨V, h1, h2, h3, fun v hv => by rw [crash_votes]; exact h4 v hv⟩

/-- The provenance invariants hold in every reachable world. -/
theorem pInv_reachable {members : List Nat} {w : World σ κ} (h : Reachable members w) :
    PInv members w := by
  induction h with
  | init => exact pInv_init members
  | tail hr hs ih => exact pInv_step (allInv_reachable hr).base.cfg ih (allInv_reachable (.tail hr hs)) hs

end RaftKV.Proof
