import RaftKV.Proof.Terms

/-!
# Which handlers can emit a vote grant

Election Safety is an argument about vote grants, so the first thing to pin
down is where a `requestVoteResp _ true` packet can possibly come from.

The answer is: only `handleRequestVote`. Every other handler emits either
`appendEntries`, `appendEntriesResp`, `requestVote`, or nothing at all. Proving
that once collapses most of the later case analysis into a contradiction.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [KVStore κ]

/-- `p` is a granted vote for term `t`. -/
def IsGrant (t : Nat) (p : Packet) : Prop := p.2.2 = Msg.requestVoteResp t true

/-- Membership in `sendsOf` reflects a `send` action. -/
theorem mem_sendsOf {i : Nat} {acts : List Action} {p : Packet} (h : p ∈ sendsOf i acts) :
    ∃ to m, p = (i, to, m) ∧ Action.send to m ∈ acts := by
  unfold sendsOf at h
  rcases List.mem_filterMap.mp h with ⟨a, ha, heq⟩
  cases a with
  | send to m => exact ⟨to, m, by simpa using heq.symm, ha⟩
  | reply _ _ _ => simp at heq
  | notLeader _ _ => simp at heq

/-- `broadcastAppend` only ever emits `appendEntries`. -/
theorem broadcastAppend_shape {s : NodeState σ κ} {to : Nat} {m : Msg}
    (h : Action.send to m ∈ broadcastAppend s) :
    ∃ t l pi pt es lc, m = Msg.appendEntries t l pi pt es lc := by
  unfold broadcastAppend at h
  rcases List.mem_map.mp h with ⟨p, _, heq⟩
  cases heq
  unfold appendEntriesTo
  exact ⟨_, _, _, _, _, _, rfl⟩

/--
`retryTo` sends only a snapshot and an `appendEntries`, both to the same peer.

This is the one lemma every "which messages can this handler emit" argument
needs about the back-off path, snapshot shipping included.
-/
theorem retryTo_shape {s : NodeState σ κ} {peer : Nat} {b : Bool} {to : Nat} {m : Msg}
    (h : Action.send to m ∈ retryTo s peer b) :
    to = peer ∧ (m = snapshotMsg s ∨ m = appendEntriesTo s peer) := by
  unfold retryTo at h
  split at h
  · rcases List.mem_cons.mp h with h' | h'
    · exact ⟨(Action.send.inj h').1, Or.inl (Action.send.inj h').2⟩
    · rcases List.mem_singleton.mp h' with h''
      exact ⟨(Action.send.inj h'').1, Or.inr (Action.send.inj h'').2⟩
  · rcases List.mem_singleton.mp h with h'
    exact ⟨(Action.send.inj h').1, Or.inr (Action.send.inj h').2⟩

/-- The back-off path emits sends only, never a client reply. -/
theorem retryTo_reply {s : NodeState σ κ} {peer : Nat} {b : Bool} {n rid : Nat} {r : Reply}
    (h : Action.reply n rid r ∈ retryTo s peer b) : False := by
  unfold retryTo at h
  split at h
  · rcases List.mem_cons.mp h with h' | h'
    · exact Action.noConfusion h'
    · rcases List.mem_singleton.mp h' with h''; exact Action.noConfusion h''
  · rcases List.mem_singleton.mp h with h'; exact Action.noConfusion h'

/-- A snapshot message is an `installSnapshot`, by definition. -/
theorem snapshotMsg_shape (s : NodeState σ κ) :
    ∃ t l li a ps, snapshotMsg s = Msg.installSnapshot t l li a ps :=
  ⟨_, _, _, _, _, rfl⟩

/-- Actions from a step-down are never sends. -/
theorem stepDown_no_send {s : NodeState σ κ} {t : Nat} {hint : Option Nat}
    {to : Nat} {m : Msg} : Action.send to m ∉ (stepDown s t hint).2 := by
  unfold stepDown
  intro h
  rcases List.mem_map.mp h with ⟨_, _, heq⟩
  exact Action.noConfusion heq

theorem maybeStepDown_no_send {s : NodeState σ κ} {t : Nat} {hint : Option Nat}
    {to : Nat} {m : Msg} : Action.send to m ∉ (maybeStepDown s t hint).2 := by
  unfold maybeStepDown
  split
  · exact stepDown_no_send
  · simp

/-- The snapshot handler sends nothing at all: it only acknowledges by acting. -/
theorem handleInstallSnapshot_no_send {s : NodeState σ κ}
    {term leaderId lastIdx : Nat} {a : Entry} {ps : List (String × String)}
    {to : Nat} {m : Msg} :
    Action.send to m ∉ (handleInstallSnapshot s term leaderId lastIdx a ps).2 := by
  rw [handleInstallSnapshot]
  split
  · simp
  · dsimp only
    split <;> exact maybeStepDown_no_send

/-- Applying committed entries emits only client replies. -/
theorem applyOne_no_send {s : NodeState σ κ} {to : Nat} {m : Msg} :
    Action.send to m ∉ (applyOne s).2 := by
  rw [applyOne]
  cases LogStore.get s.log (s.lastApplied + 1) with
  | none => simp
  | some e => dsimp only; split <;> simp

theorem applyLoop_send {f : Nat} {s : NodeState σ κ} {acc : List Action} {to : Nat} {m : Msg}
    (h : Action.send to m ∈ (applyLoop f s acc).2) : Action.send to m ∈ acc := by
  induction f generalizing s acc with
  | zero => simpa [applyLoop] using h
  | succ n ih =>
      rw [applyLoop] at h
      split at h
      · have := ih h
        rcases List.mem_append.mp this with h' | h'
        · exact h'
        · exact absurd h' applyOne_no_send
      · simpa using h

theorem applyCommitted_no_send {s : NodeState σ κ} {to : Nat} {m : Msg} :
    Action.send to m ∉ (applyCommitted s).2 := by
  intro h
  simpa using applyLoop_send h

/-! ## Per-handler shape lemmas -/

/-- Assuming leadership only broadcasts `appendEntries`. -/
theorem becomeLeader_send {s : NodeState σ κ} {to : Nat} {m : Msg}
    (h : Action.send to m ∈ (becomeLeader s).2) :
    ∃ t l pi pt es lc, m = Msg.appendEntries t l pi pt es lc := by
  rw [becomeLeader] at h
  exact broadcastAppend_shape h

theorem handleRequestVoteResp_no_grant {s : NodeState σ κ} {term : Nat} {g : Bool} {src : Nat}
    {to : Nat} {t : Nat} :
    Action.send to (Msg.requestVoteResp t true) ∉ (handleRequestVoteResp s term g src).2 := by
  rw [handleRequestVoteResp]
  split
  · exact stepDown_no_send
  · split
    · simp
    · dsimp only
      split <;> split
      all_goals
        first
        | simp
        | (intro h
           rcases becomeLeader_send h with ⟨_, _, _, _, _, _, heq⟩
           exact Msg.noConfusion heq)

theorem appendEntriesTo_shape (s : NodeState σ κ) (p : Nat) :
    ∃ t l pi pt es lc, appendEntriesTo s p = Msg.appendEntries t l pi pt es lc := by
  unfold appendEntriesTo; exact ⟨_, _, _, _, _, _, rfl⟩

theorem handleAppendEntries_no_grant {s : NodeState σ κ}
    {src term leaderId prevIdx prevTerm : Nat} {es : List Entry} {lc to t : Nat} :
    Action.send to (Msg.requestVoteResp t true)
      ∉ (handleAppendEntries s src term leaderId prevIdx prevTerm es lc).2 := by
  rw [handleAppendEntries]
  split
  · simp
  · dsimp only
    split
    · intro h
      rcases List.mem_append.mp h with h' | h'
      · exact maybeStepDown_no_send h'
      · simp at h'
    · dsimp only
      intro h
      rcases List.mem_append.mp h with h' | h'
      · exact maybeStepDown_no_send h'
      · rcases List.mem_cons.mp h' with h'' | h''
        · exact Msg.noConfusion (Action.send.inj h'').2
        · exact applyCommitted_no_send h''

theorem handleAppendEntriesResp_no_grant {s : NodeState σ κ}
    {src term : Nat} {ok : Bool} {matchIdx to t : Nat} :
    Action.send to (Msg.requestVoteResp t true)
      ∉ (handleAppendEntriesResp s src term ok matchIdx).2 := by
  rw [handleAppendEntriesResp]
  split
  · exact stepDown_no_send
  · split
    · simp
    · split
      · exact applyCommitted_no_send
      · dsimp only
        intro h
        rcases (retryTo_shape h).2 with h' | h' <;>
          exact absurd h' (by simp [snapshotMsg, appendEntriesTo])

theorem handleClientReq_no_grant {s : NodeState σ κ} {rid : Nat} {c : Command} {to t : Nat} :
    Action.send to (Msg.requestVoteResp t true) ∉ (handleClientReq s rid c).2 := by
  rw [handleClientReq]
  split
  · simp
  · dsimp only
    intro h
    rcases List.mem_append.mp h with h' | h'
    · rcases broadcastAppend_shape h' with ⟨_, _, _, _, _, _, heq⟩
      exact Msg.noConfusion heq
    · exact applyCommitted_no_send h'

theorem startElection_no_grant {s : NodeState σ κ} {to t : Nat} :
    Action.send to (Msg.requestVoteResp t true) ∉ (startElection s).2 := by
  rw [startElection]
  dsimp only
  split
  · intro h
    rcases becomeLeader_send h with ⟨_, _, _, _, _, _, heq⟩
    exact Msg.noConfusion heq
  · intro h
    rcases List.mem_map.mp h with ⟨_, _, heq⟩
    exact Msg.noConfusion (Action.send.inj heq).2

/-! ## Exact send shapes

Sharper than the "cannot emit X" lemmas: each of these says precisely which
message constructor a handler is capable of transmitting.
-/

theorem handleRequestVote_send_shape {s : NodeState σ κ} {src term candId li lt to : Nat}
    {m : Msg} (h : Action.send to m ∈ (handleRequestVote s src term candId li lt).2) :
    ∃ t g, m = Msg.requestVoteResp t g := by
  rw [handleRequestVote] at h
  split at h
  · exact ⟨_, _, (Action.send.inj (List.mem_singleton.mp h)).2⟩
  · dsimp only at h
    split at h <;>
      (rcases List.mem_append.mp h with h' | h'
       · exact absurd h' maybeStepDown_no_send
       · exact ⟨_, _, (Action.send.inj (List.mem_singleton.mp h')).2⟩)

theorem handleAppendEntries_send_shape {s : NodeState σ κ}
    {src term leaderId prevIdx prevTerm : Nat} {es : List Entry} {lc to : Nat} {m : Msg}
    (h : Action.send to m ∈ (handleAppendEntries s src term leaderId prevIdx prevTerm es lc).2) :
    ∃ t ok mi, m = Msg.appendEntriesResp t ok mi := by
  rw [handleAppendEntries] at h
  split at h
  · exact ⟨_, _, _, (Action.send.inj (List.mem_singleton.mp h)).2⟩
  · dsimp only at h
    split at h
    · rcases List.mem_append.mp h with h' | h'
      · exact absurd h' maybeStepDown_no_send
      · exact ⟨_, _, _, (Action.send.inj (List.mem_singleton.mp h')).2⟩
    · dsimp only at h
      rcases List.mem_append.mp h with h' | h'
      · exact absurd h' maybeStepDown_no_send
      · rcases List.mem_cons.mp h' with h'' | h''
        · exact ⟨_, _, _, (Action.send.inj h'').2⟩
        · exact absurd h'' applyCommitted_no_send

/-! ## Where `requestVote` messages come from -/

theorem handleRequestVote_no_rv {s : NodeState σ κ} {src term candId li lt : Nat}
    {to t c li' lt' : Nat} :
    Action.send to (Msg.requestVote t c li' lt') ∉ (handleRequestVote s src term candId li lt).2 := by
  rw [handleRequestVote]
  split
  · simp
  · dsimp only
    split <;>
      (intro h
       rcases List.mem_append.mp h with h' | h'
       · exact maybeStepDown_no_send h'
       · simp at h')

theorem handleRequestVoteResp_no_rv {s : NodeState σ κ} {term : Nat} {g : Bool} {src : Nat}
    {to t c li lt : Nat} :
    Action.send to (Msg.requestVote t c li lt) ∉ (handleRequestVoteResp s term g src).2 := by
  rw [handleRequestVoteResp]
  split
  · exact stepDown_no_send
  · split
    · simp
    · dsimp only
      split <;> split
      all_goals
        first
        | simp
        | (intro h
           rcases becomeLeader_send h with ⟨_, _, _, _, _, _, heq⟩
           exact Msg.noConfusion heq)

theorem handleAppendEntries_no_rv {s : NodeState σ κ}
    {src term leaderId prevIdx prevTerm : Nat} {es : List Entry} {lc to t c li lt : Nat} :
    Action.send to (Msg.requestVote t c li lt)
      ∉ (handleAppendEntries s src term leaderId prevIdx prevTerm es lc).2 := by
  rw [handleAppendEntries]
  split
  · simp
  · dsimp only
    split
    · intro h
      rcases List.mem_append.mp h with h' | h'
      · exact maybeStepDown_no_send h'
      · simp at h'
    · dsimp only
      intro h
      rcases List.mem_append.mp h with h' | h'
      · exact maybeStepDown_no_send h'
      · rcases List.mem_cons.mp h' with h'' | h''
        · exact Msg.noConfusion (Action.send.inj h'').2
        · exact applyCommitted_no_send h''

theorem handleAppendEntriesResp_no_rv {s : NodeState σ κ}
    {src term : Nat} {ok : Bool} {matchIdx to t c li lt : Nat} :
    Action.send to (Msg.requestVote t c li lt)
      ∉ (handleAppendEntriesResp s src term ok matchIdx).2 := by
  rw [handleAppendEntriesResp]
  split
  · exact stepDown_no_send
  · split
    · simp
    · split
      · exact applyCommitted_no_send
      · dsimp only
        intro h
        rcases (retryTo_shape h).2 with h' | h' <;>
          exact absurd h' (by simp [snapshotMsg, appendEntriesTo])

theorem handleClientReq_no_rv {s : NodeState σ κ} {rid : Nat} {cmd : Command}
    {to t c li lt : Nat} :
    Action.send to (Msg.requestVote t c li lt) ∉ (handleClientReq s rid cmd).2 := by
  rw [handleClientReq]
  split
  · simp
  · dsimp only
    intro h
    rcases List.mem_append.mp h with h' | h'
    · rcases broadcastAppend_shape h' with ⟨_, _, _, _, _, _, heq⟩
      exact Msg.noConfusion heq
    · exact applyCommitted_no_send h'

/-- A candidate always names *itself* in the `requestVote` it sends. -/
theorem startElection_rv_cid {s : NodeState σ κ} {to t c li lt : Nat}
    (h : Action.send to (Msg.requestVote t c li lt) ∈ (startElection s).2) :
    c = s.cfg.me := by
  rw [startElection] at h
  dsimp only at h
  split at h
  · rcases becomeLeader_send h with ⟨_, _, _, _, _, _, heq⟩
    exact absurd heq (by simp)
  · rcases List.mem_map.mp h with ⟨_, _, heq⟩
    exact ((Msg.requestVote.inj (Action.send.inj heq).2)).2.1.symm

/--
**A `requestVote` advertises exactly the sender's own log.**

The index and term it carries are the sender's `lastIndex` and `lastTerm` at the
moment it campaigns, and campaigning does not disturb the log. This is what ties
the `upToDate` check on the voter's side to a real property of the candidate.
-/
theorem step_requestVote_log {s : NodeState σ κ} {ev : Event} {to U cid li lt : Nat}
    (h : Action.send to (Msg.requestVote U cid li lt) ∈ (Protocol.step s ev).2) :
    li = LogStore.lastIndex s.log ∧ lt = LogStore.lastTerm s.log
      ∧ (Protocol.step s ev).1.currentTerm = U
      ∧ (Protocol.step s ev).1.log = s.log
      ∧ (Protocol.step s ev).1.role = Role.candidate
      ∧ s.currentTerm < U := by
  cases ev with
  | recv src m =>
      cases m with
      | requestVote a b c d => exact absurd h handleRequestVote_no_rv
      | requestVoteResp a b => exact absurd h handleRequestVoteResp_no_rv
      | appendEntries a b c d e f => exact absurd h handleAppendEntries_no_rv
      | appendEntriesResp a b c => exact absurd h handleAppendEntriesResp_no_rv
      | installSnapshot a b c d e => exact absurd h handleInstallSnapshot_no_send
  | clientReq rid cmd => exact absurd h handleClientReq_no_rv
  | electionTimeout =>
      rw [Protocol.step] at h ⊢
      split at h
      · simp at h
      · rename_i hlead
        rw [if_neg hlead] at *
        rw [startElection] at h ⊢
        dsimp only at h ⊢
        split at h
        · rcases becomeLeader_send h with ⟨_, _, _, _, _, _, heq⟩
          exact absurd heq (by simp)
        · rename_i hmaj
          rw [if_neg hmaj]
          rcases List.mem_map.mp h with ⟨p, _, heq⟩
          have hm := (Action.send.inj heq).2
          obtain ⟨hU, _, hli, hlt⟩ := Msg.requestVote.inj hm
          exact ⟨hli.symm, hlt.symm, hU, rfl, rfl, by omega⟩
  | heartbeatTimeout =>
      rw [Protocol.step] at h
      split at h
      · rcases broadcastAppend_shape h with ⟨_, _, _, _, _, _, heq⟩
        exact absurd heq (by simp)
      · simp at h

/--
**A `requestVote` always carries its sender's own id.**

Consequently a granted vote recorded against candidate `c` really is a vote for
the node that asked, which is what lets `VoteInv` speak about the recipient of
the response.
-/
theorem step_requestVote_cid {s : NodeState σ κ} {ev : Event} {to t c li lt : Nat}
    (h : Action.send to (Msg.requestVote t c li lt) ∈ (Protocol.step s ev).2) :
    c = s.cfg.me := by
  cases ev with
  | recv src m =>
      cases m with
      | requestVote a b d e => exact absurd h handleRequestVote_no_rv
      | requestVoteResp a b => exact absurd h handleRequestVoteResp_no_rv
      | appendEntries a b d e f g => exact absurd h handleAppendEntries_no_rv
      | appendEntriesResp a b d => exact absurd h handleAppendEntriesResp_no_rv
      | installSnapshot a b c d e => exact absurd h handleInstallSnapshot_no_send
  | clientReq rid cmd => exact absurd h handleClientReq_no_rv
  | electionTimeout =>
      rw [Protocol.step] at h
      split at h
      · simp at h
      · exact startElection_rv_cid h
  | heartbeatTimeout =>
      rw [Protocol.step] at h
      split at h
      · rcases broadcastAppend_shape h with ⟨_, _, _, _, _, _, heq⟩
        exact absurd heq (by simp)
      · simp at h


/-! ## No handler but `handleAppendEntries` acknowledges -/

theorem handleRequestVoteResp_no_aer {s : NodeState σ κ} {term : Nat} {g : Bool} {src : Nat}
    {to t m : Nat} {ok : Bool} :
    Action.send to (Msg.appendEntriesResp t ok m) ∉ (handleRequestVoteResp s term g src).2 := by
  rw [handleRequestVoteResp]
  split
  · exact stepDown_no_send
  · split
    · simp
    · dsimp only
      split <;> split
      all_goals
        first
        | simp
        | (intro h
           rcases becomeLeader_send h with ⟨_, _, _, _, _, _, heq⟩
           exact Msg.noConfusion heq)

theorem handleAppendEntriesResp_no_aer {s : NodeState σ κ}
    {src term : Nat} {ok0 : Bool} {matchIdx to t m : Nat} {ok : Bool} :
    Action.send to (Msg.appendEntriesResp t ok m)
      ∉ (handleAppendEntriesResp s src term ok0 matchIdx).2 := by
  rw [handleAppendEntriesResp]
  split
  · exact stepDown_no_send
  · split
    · simp
    · split
      · exact applyCommitted_no_send
      · dsimp only
        intro h
        rcases (retryTo_shape h).2 with h' | h' <;>
          exact absurd h' (by simp [snapshotMsg, appendEntriesTo])

theorem handleClientReq_no_aer {s : NodeState σ κ} {rid : Nat} {cmd : Command}
    {to t m : Nat} {ok : Bool} :
    Action.send to (Msg.appendEntriesResp t ok m) ∉ (handleClientReq s rid cmd).2 := by
  rw [handleClientReq]
  split
  · simp
  · dsimp only
    intro h
    rcases List.mem_append.mp h with h' | h'
    · rcases broadcastAppend_shape h' with ⟨_, _, _, _, _, _, heq⟩
      exact Msg.noConfusion heq
    · exact applyCommitted_no_send h'

theorem startElection_no_aer {s : NodeState σ κ} {to t m : Nat} {ok : Bool} :
    Action.send to (Msg.appendEntriesResp t ok m) ∉ (startElection s).2 := by
  rw [startElection]
  dsimp only
  split
  · intro h
    rcases becomeLeader_send h with ⟨_, _, _, _, _, _, heq⟩
    exact Msg.noConfusion heq
  · intro h
    rcases List.mem_map.mp h with ⟨_, _, heq⟩
    exact Msg.noConfusion (Action.send.inj heq).2

/--
**Only `handleRequestVote` grants votes.** If a step emits a granted vote for
term `t`, the event being handled was a `requestVote`.
-/
theorem grant_only_from_requestVote {s : NodeState σ κ} {ev : Event} {to t : Nat}
    (h : Action.send to (Msg.requestVoteResp t true) ∈ (Protocol.step s ev).2) :
    ∃ src term candId li lt, ev = Event.recv src (Msg.requestVote term candId li lt) := by
  cases ev with
  | recv src m =>
      cases m with
      | requestVote term candId li lt => exact ⟨src, term, candId, li, lt, rfl⟩
      | requestVoteResp a b => exact absurd h handleRequestVoteResp_no_grant
      | appendEntries a b c d e f => exact absurd h handleAppendEntries_no_grant
      | appendEntriesResp a b c => exact absurd h handleAppendEntriesResp_no_grant
      | installSnapshot a b c d e => exact absurd h handleInstallSnapshot_no_send
  | clientReq rid c => exact absurd h handleClientReq_no_grant
  | electionTimeout =>
      rw [Protocol.step] at h
      split at h
      · simp at h
      · exact absurd h startElection_no_grant
  | heartbeatTimeout =>
      rw [Protocol.step] at h
      split at h
      · rcases broadcastAppend_shape h with ⟨_, _, _, _, _, _, heq⟩
        exact Msg.noConfusion heq
      · simp at h

end RaftKV.Proof
