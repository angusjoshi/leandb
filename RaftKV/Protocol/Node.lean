import RaftKV.Protocol.Types
import RaftKV.Storage.Log
import RaftKV.Storage.KV

/-!
# The Raft node as a pure function

`step : NodeState σ κ → Event → NodeState σ κ × List Action`.

No `IO`, no sockets, no clock. The runtime supplies `Event`s and executes
`Action`s; everything decided here is a deterministic function of the state and
the event. Two consequences:

* the safety proofs in `RaftKV.Proof` are proofs about a pure function, needing
  no program logic at all; and
* the deterministic simulator in `RaftKV.Runtime.Sim` can replay any schedule
  exactly, because a node's behaviour has no hidden inputs.

The node is generic in the log `σ` and state machine `κ`, so nothing here — and
nothing downstream — is tied to `ArrayLog` or `HashKV`.
-/

namespace RaftKV.Protocol

open RaftKV LogStore KVStore

variable {σ κ : Type} [LogStore σ] [KVStore κ]

/-- The state of a freshly started replica. -/
def initState (cfg : Config) : NodeState σ κ where
  cfg := cfg
  currentTerm := 0
  votedFor := none
  log := LogStore.empty
  commitIndex := 0
  lastApplied := 0
  role := .follower
  votesGranted := []
  nextIndex := PeerMap.empty
  matchIndex := PeerMap.empty
  kv := KVStore.empty
  snapIndex := 0
  snapKV := KVStore.empty
  sessions := []
  snapSessions := []
  pending := []
  leaderHint := none

/--
**Restart after a crash.** Volatile state is lost; durable state survives.

Raft's durable trio is `currentTerm`, `votedFor` and the log. Everything else —
role, commit and applied indices, the state machine, peer progress and pending
client requests — is rebuilt from scratch: the state machine by replaying the
log, which is why losing it costs nothing.

Coming back as a *follower* is what makes a restart cheap to reason about: it
discards any candidacy or leadership in flight, and the only route back to
candidacy (`startElection`) strictly advances the term, so a node can never
campaign twice in one term.
-/
structure Persistent (σ : Type) where
  /-- The latest term this node has seen. -/
  currentTerm : Nat
  /-- Who it voted for in that term, if anyone. -/
  votedFor : Option Nat
  /-- The replicated log. -/
  log : σ
  /-- The index the snapshot covers. -/
  snapIndex : Nat
  /-- The state machine as of that index, as bindings. -/
  snapPairs : List (String × String)
  /-- The requests it had already carried out. -/
  snapSessions : List Nat
  deriving Repr, DecidableEq

/-- The part of a node's state that must outlive a crash. -/
def persistOf (s : NodeState σ κ) : Persistent σ :=
  ⟨s.currentTerm, s.votedFor, s.log, s.snapIndex, KVStore.toPairs s.snapKV, s.snapSessions⟩

/--
Rebuild a node from its configuration and whatever the device gave back.

The state machine restarts from the snapshot rather than from empty, and
`lastApplied` with it: the entries the snapshot covers may no longer be in the
log to replay.
-/
def recoverNode (cfg : Config) (p : Persistent σ) : NodeState σ κ :=
  { (initState cfg : NodeState σ κ) with
      currentTerm := p.currentTerm, votedFor := p.votedFor, log := p.log,
      snapIndex := p.snapIndex, snapKV := KVStore.ofPairs p.snapPairs,
      kv := KVStore.ofPairs p.snapPairs,
      snapSessions := p.snapSessions, sessions := p.snapSessions,
      lastApplied := p.snapIndex, commitIndex := p.snapIndex }

def restart (s : NodeState σ κ) : NodeState σ κ := recoverNode s.cfg (persistOf s)

/--
**Log compaction.** Discard everything the state machine has already absorbed,
recording the state machine itself in its place.

The cut is at `lastApplied`: everything strictly below it goes, and the entry
*at* it stays. That entry is already covered by the snapshot and will never be
replayed, but it must remain in the log, because it is the anchor a leader
names in `prevLogIndex` when it replicates `lastApplied + 1`. Discarding it
would leave the leader unable to serve its own first live entry to anybody.

So after a compaction `firstIndex = snapIndex`, and `snapIndex` is either `0`
(nothing discarded) or at least `2`. The lower bound matters: at `snapIndex = 1`
the window would still start at `1`, and a payload anchored at the virtual index
`0` could overwrite the snapshotted entry.

A no-op unless there is something to discard and something to keep.
-/
def compactTo (s : NodeState σ κ) : NodeState σ κ :=
  if 2 ≤ s.lastApplied ∧ LogStore.firstIndex s.log ≤ s.lastApplied
      ∧ s.lastApplied ≤ LogStore.lastIndex s.log then
    { s with log := LogStore.compact s.log s.lastApplied,
             snapIndex := s.lastApplied, snapKV := s.kv, snapSessions := s.sessions }
  else s

/-- **Restarting is exactly recovering from the durable projection.** -/
theorem restart_eq_recoverNode (s : NodeState σ κ) :
    restart s = recoverNode s.cfg (persistOf s) := rfl

/-! ## Helpers -/

/--
Revert to follower in a strictly newer term, abandoning any votes held and
failing any client requests this node had accepted but not yet committed.
-/
def stepDown (s : NodeState σ κ) (term : Nat) (hint : Option Nat) :
    NodeState σ κ × List Action :=
  ({ s with currentTerm := term, votedFor := none, role := .follower,
            votesGranted := [], pending := [], leaderHint := hint },
   s.pending.map (fun p => Action.notLeader p.2 hint))

/-- Step down only if the incoming term is genuinely newer; otherwise stay put. -/
def maybeStepDown (s : NodeState σ κ) (term : Nat) (hint : Option Nat) :
    NodeState σ κ × List Action :=
  if term > s.currentTerm then stepDown s term hint else (s, [])

/--
Is a candidate's log at least as up to date as ours? This is the check that
makes Leader Completeness work: a candidate missing committed entries cannot
collect a quorum.
-/
def upToDate (s : NodeState σ κ) (candLastIdx candLastTerm : Nat) : Bool :=
  candLastTerm > LogStore.lastTerm s.log ||
    (candLastTerm == LogStore.lastTerm s.log && candLastIdx ≥ LogStore.lastIndex s.log)

/--
May we grant `candId` our vote? Only if we have not already voted for someone
else this term, and the candidate's log is at least as up to date as ours.
-/
def voteGranted (s : NodeState σ κ) (candId candLastIdx candLastTerm : Nat) : Bool :=
  (s.votedFor == none) && upToDate s candLastIdx candLastTerm

/--
Splice `entries` into the log starting at `startIdx`, truncating on the first
conflicting term. Matching entries are left alone, which is what makes
`AppendEntries` idempotent under duplication and reordering.
-/
def appendFrom (lg : σ) (startIdx : Nat) : List Entry → σ
  | [] => lg
  | e :: es =>
    match LogStore.get lg startIdx with
    | some existing =>
        if existing.term == e.term then
          appendFrom lg (startIdx + 1) es
        else
          appendFrom (LogStore.append (LogStore.truncFrom lg startIdx) e) (startIdx + 1) es
    | none => appendFrom (LogStore.append lg e) (startIdx + 1) es

/-- Apply the single entry at `lastApplied + 1`, replying if a client is waiting. -/
def applyOne (s : NodeState σ κ) : NodeState σ κ × List Action :=
  let i := s.lastApplied + 1
  match LogStore.get s.log i with
  | none => (s, [])
  | some e =>
    -- **Exactly once.** A write whose request this replica has already carried
    -- out is not carried out again; the client is told `ok`, which is the only
    -- answer a write ever has. Reads are always executed: a retried read is a
    -- second operation, not a duplicate.
    let dup := Spec.isWrite e.cmd && s.sessions.contains e.reqId
    let (kv', r) := if dup then (s.kv, Reply.ok) else KVStore.applyCmd s.kv e.cmd
    let sess := if Spec.isWrite e.cmd && !s.sessions.contains e.reqId then
        e.reqId :: s.sessions else s.sessions
    let acts := if s.pending.any (fun p => p.1 == i) then [Action.reply i e.reqId r] else []
    ({ s with kv := kv', sessions := sess, lastApplied := i,
              pending := s.pending.filter (fun p => p.1 != i) }, acts)

/-- Apply committed-but-unapplied entries, bounded by explicit fuel. -/
def applyLoop : Nat → NodeState σ κ → List Action → NodeState σ κ × List Action
  | 0, s, acc => (s, acc)
  | fuel + 1, s, acc =>
    if s.lastApplied < s.commitIndex then
      let (s', acts) := applyOne s
      applyLoop fuel s' (acc ++ acts)
    else (s, acc)

/-- Drive the state machine forward to `commitIndex`. -/
def applyCommitted (s : NodeState σ κ) : NodeState σ κ × List Action :=
  applyLoop (s.commitIndex - s.lastApplied) s []

/-- The `AppendEntries` a leader should currently send to `peer`. -/
def appendEntriesTo (s : NodeState σ κ) (peer : Nat) : Msg :=
  -- Clamp the slice start to the send floor: the lowest index whose predecessor
  -- this node can still name. `sendFloor` is `1` until something has been
  -- compacted away, so this is the old `max 1` unchanged until the first
  -- compaction; afterwards it stops the leader from claiming a term for an
  -- entry it has discarded.
  let ni := max (LogStore.sendFloor s.log)
    (PeerMap.get s.nextIndex peer (LogStore.lastIndex s.log + 1))
  let prevIdx := ni - 1
  let prevTerm := (LogStore.termAt s.log prevIdx).getD 0
  .appendEntries s.currentTerm s.cfg.me prevIdx prevTerm (LogStore.sliceFrom s.log ni) s.commitIndex

/--
The snapshot a leader ships to a follower it can no longer serve from the log.

The anchor is the entry at `snapIndex`, which compaction deliberately keeps, so
this never has to reconstruct anything.
-/
def snapshotMsg (s : NodeState σ κ) : Msg :=
  .installSnapshot s.currentTerm s.cfg.me s.snapIndex
    ((LogStore.get s.log s.snapIndex).getD default) (KVStore.toPairs s.snapKV, s.snapSessions)

/--
What a leader sends a follower whose last `AppendEntries` was rejected: the
retry, preceded by a snapshot when the retry alone could not possibly succeed.

Kept as its own definition so that "what this handler can send" is one lemma
rather than a case split repeated at every site that needs it.
-/
def retryTo (s : NodeState σ κ) (peer : Nat) (snap : Bool) : List Action :=
  if snap then [Action.send peer (snapshotMsg s), Action.send peer (appendEntriesTo s peer)]
  else [Action.send peer (appendEntriesTo s peer)]

/-- Send the appropriate `AppendEntries` to every peer. -/
def broadcastAppend (s : NodeState σ κ) : List Action :=
  s.cfg.peers.map (fun p => Action.send p (appendEntriesTo s p))

/--
Advance `commitIndex` to the highest index replicated on a majority **whose
entry belongs to the current term**.

That last condition is Raft's Figure-8 fix. Committing an older-term entry just
because it is present on a majority is unsound: a later leader could still
overwrite it.
-/
def replicatedOn (s : NodeState σ κ) (n : Nat) : List Nat :=
  s.cfg.me :: s.cfg.peers.filter (fun p => PeerMap.get s.matchIndex p 0 ≥ n)

/-- May index `n` be committed? -/
def commitOk (s : NodeState σ κ) (n : Nat) : Bool :=
  n > s.commitIndex && LogStore.termAt s.log n == some s.currentTerm &&
    s.cfg.isMajority (replicatedOn s n)

/-- Committable indices, highest first. -/
def commitCandidates (s : NodeState σ κ) : List Nat :=
  ((List.range (LogStore.lastIndex s.log + 1)).filter (commitOk s)).reverse

def advanceCommit (s : NodeState σ κ) : NodeState σ κ :=
  match (commitCandidates s).head? with
  | none => s
  | some n => { s with commitIndex := n }

/-- Assume leadership: reset peer progress tracking and assert authority. -/
def becomeLeader (s : NodeState σ κ) : NodeState σ κ × List Action :=
  let s' := { s with role := .leader, leaderHint := some s.cfg.me,
                     nextIndex := PeerMap.setAll s.cfg.peers (LogStore.lastIndex s.log + 1),
                     matchIndex := PeerMap.setAll s.cfg.peers 0 }
  (s', broadcastAppend s')

/-- Increment the term and campaign. -/
def startElection (s : NodeState σ κ) : NodeState σ κ × List Action :=
  let t := s.currentTerm + 1
  let s' := { s with currentTerm := t, votedFor := some s.cfg.me, role := .candidate,
                     votesGranted := [s.cfg.me], leaderHint := none }
  if s'.cfg.isMajority s'.votesGranted then
    -- Single-node cluster: our own vote is already a quorum.
    becomeLeader s'
  else
    let msg := Msg.requestVote t s.cfg.me (LogStore.lastIndex s.log) (LogStore.lastTerm s.log)
    (s', s.cfg.peers.map (fun p => Action.send p msg))

/-! ## Message handlers -/

/-- Decide whether to grant a vote. -/
def handleRequestVote (s : NodeState σ κ) (src term candId candLastIdx candLastTerm : Nat) :
    NodeState σ κ × List Action :=
  if term < s.currentTerm then
    (s, [Action.send src (.requestVoteResp s.currentTerm false)])
  else
    let sd := maybeStepDown s term none
    let s := sd.1
    if voteGranted s candId candLastIdx candLastTerm then
      ({ s with votedFor := some candId },
       sd.2 ++ [Action.send src (.requestVoteResp s.currentTerm true)])
    else
      (s, sd.2 ++ [Action.send src (.requestVoteResp s.currentTerm false)])

/-- Tally a vote; assume leadership on reaching a quorum. -/
def handleRequestVoteResp (s : NodeState σ κ) (term : Nat) (granted : Bool) (src : Nat) :
    NodeState σ κ × List Action :=
  if term > s.currentTerm then
    stepDown s term none
  else if s.role != .candidate || term != s.currentTerm || !granted then
    (s, [])
  else
    let votes := if s.votesGranted.contains src then s.votesGranted else src :: s.votesGranted
    let s' := { s with votesGranted := votes }
    if s'.cfg.isMajority votes then becomeLeader s' else (s', [])

/--
Does this `AppendEntries` pass both of the receiver's checks?

Factored out because the ghost logical log in `RaftKV.Protocol.Network` has to
make the same decision, and a second copy of the condition could drift from this
one. `maybeStepDown` does not touch the log, so evaluating the consistency check
against the pre-state's log is the same as evaluating it after the step down.
-/
def aeConsistent (s : NodeState σ κ) (prevIdx prevTerm : Nat) : Bool :=
  (prevIdx == 0 && LogStore.firstIndex s.log == 1)
    || LogStore.termAt s.log prevIdx == some prevTerm

/-- The consistency check looks only at the log. -/
theorem aeConsistent_congr {a b : NodeState σ κ} (h : a.log = b.log) (prevIdx prevTerm : Nat) :
    aeConsistent a prevIdx prevTerm = aeConsistent b prevIdx prevTerm := by
  unfold aeConsistent; rw [h]

/-- Both of the receiver's checks together. -/
def aeAccepts (s : NodeState σ κ) (term prevIdx prevTerm : Nat) : Bool :=
  !(decide (term < s.currentTerm)) && aeConsistent s prevIdx prevTerm

/-- Does the receiver already hold the snapshot's anchor entry? -/
def snapHeld (s : NodeState σ κ) (lastIdx : Nat) (anchor : Entry) : Bool :=
  LogStore.termAt s.log lastIdx == some anchor.term

/--
Will this snapshot actually be installed?

Four ways it is not: the sender is stale; the receiver already holds the anchor
and so needs nothing; the snapshot does not reach past what the receiver already
considers committed, so installing it would throw away committed entries; or it
does not cover the receiver's whole log, so installing it would drop entries the
receiver had acknowledged. `2 ≤ lastIdx` is the same lower bound `compactTo`
maintains.

That last condition is a real restriction, and it is why this is not a complete
answer to catching a follower up: a follower whose log runs *past* the leader's
snapshot point but disagrees below it still cannot be served. Such a follower is
holding uncommitted entries from an older term above a committed prefix it does
not have. Fixing that needs the snapshot to replace a prefix while retaining the
tail, which is a larger change; the common case — a follower that has simply
fallen behind — is covered.

Factored out because the model in `RaftKV.Protocol.Network` has to make the same
decision about the ghost logical log, and a second copy of the condition could
drift from this one.
-/
def snapInstalls (s : NodeState σ κ) (term lastIdx : Nat) (anchor : Entry) : Bool :=
  !(decide (term < s.currentTerm)) && !snapHeld s lastIdx anchor
    && decide (2 ≤ lastIdx) && decide (s.commitIndex < lastIdx)
    && decide (LogStore.lastIndex s.log ≤ lastIdx)

/--
Follower side of snapshot transfer.

**No message goes back.** A snapshot is always sent together with the
`AppendEntries` that follows it, and it is that message the follower
acknowledges; replying here would add a second acknowledgement site to the
protocol for no gain, and every commit-quorum argument would have to be
re-proved against it.

Leader contact spends the term's vote, exactly as `handleAppendEntries` does —
which is what keeps the change-attribution argument's witness term strictly
below the term of any vote the node goes on to cast.
-/
def handleInstallSnapshot (s : NodeState σ κ)
    (term leaderId lastIdx : Nat) (anchor : Entry)
    (pairs : List (String × String) × List Nat) : NodeState σ κ × List Action :=
  if term < s.currentTerm then
    (s, [])
  else
    let sd := maybeStepDown s term (some leaderId)
    let vf := some (sd.1.votedFor.getD leaderId)
    let s' := { sd.1 with role := .follower, leaderHint := some leaderId, votedFor := vf }
    if snapInstalls s term lastIdx anchor then
      let kv' := KVStore.ofPairs pairs.1
      ({ s' with log := LogStore.fromAnchor lastIdx anchor,
                 snapIndex := lastIdx, snapKV := kv', kv := kv',
                 snapSessions := pairs.2, sessions := pairs.2,
                 lastApplied := lastIdx, commitIndex := lastIdx }, sd.2)
    else
      (s', sd.2)

/-- Follower side of log replication. -/
def handleAppendEntries (s : NodeState σ κ)
    (src term leaderId prevIdx prevTerm : Nat) (entries : List Entry) (leaderCommit : Nat) :
    NodeState σ κ × List Action :=
  if term < s.currentTerm then
    (s, [Action.send src (.appendEntriesResp s.currentTerm false 0)])
  else
    let sd := maybeStepDown s term (some leaderId)
    let downActs := sd.2
    let vf := some (sd.1.votedFor.getD leaderId)
    let s' := { sd.1 with role := .follower, leaderHint := some leaderId, votedFor := vf }
    -- The consistency check, plus the requirement that the splice start inside
    -- the live window. `firstIndex` is `1` until something has been compacted,
    -- so the first disjunct is the old `prevIdx == 0` case unchanged; once a
    -- prefix is gone, a payload that would land in it is refused and the leader
    -- backs off (or, when it too has discarded that far, sends a snapshot).
    -- Evaluated against the *incoming* state, whose log `maybeStepDown` does not
    -- touch, so that `aeAccepts` names this very decision.
    let consistent := aeConsistent s prevIdx prevTerm
    if !consistent then
      (s', downActs ++ [Action.send src (.appendEntriesResp s'.currentTerm false 0)])
    else
      let lg := appendFrom s'.log (prevIdx + 1) entries
      let matchIdx := prevIdx + entries.length
      let s'' := { s' with log := lg }
      -- never move the commit index backwards: a stale or short payload must not
      -- retract what this node already considers committed
      let s''' := { s'' with
        commitIndex := max s''.commitIndex (min leaderCommit (LogStore.lastIndex lg)) }
      let ac := applyCommitted s'''
      (ac.1, downActs ++ Action.send src (.appendEntriesResp ac.1.currentTerm true matchIdx)
            :: ac.2)

/-- Leader side of log replication: track progress and advance the commit index. -/
def handleAppendEntriesResp (s : NodeState σ κ)
    (src term : Nat) (success : Bool) (matchIdx : Nat) : NodeState σ κ × List Action :=
  if term > s.currentTerm then
    stepDown s term none
  else if s.role != .leader || term != s.currentTerm then
    (s, [])
  else if success then
    let s := { s with matchIndex := PeerMap.set s.matchIndex src matchIdx,
                      nextIndex := PeerMap.set s.nextIndex src (matchIdx + 1) }
    applyCommitted (advanceCommit s)
  else
    -- Log divergence: back up one index and retry, but never below the window.
    let ni := PeerMap.get s.nextIndex src (LogStore.lastIndex s.log + 1)
    let s' := { s with
      nextIndex := PeerMap.set s.nextIndex src (max (LogStore.sendFloor s.log) (ni - 1)) }
    -- Once the back-off has bottomed out at the window there is nothing further
    -- to try: the follower needs entries this node no longer has. Ship the
    -- snapshot ahead of the retry, so the retry lands on an anchor the follower
    -- now holds. Nothing is sent when nothing has been discarded — an
    -- uncompacted log can always be replicated from index 1.
    (s', retryTo s' src (LogStore.firstIndex s.log != 1 && decide (ni ≤ LogStore.sendFloor s.log)))

/-- Accept a client command, or redirect if this node is not the leader. -/
def handleClientReq (s : NodeState σ κ) (reqId : Nat) (cmd : Command) :
    NodeState σ κ × List Action :=
  if s.role != .leader then
    (s, [Action.notLeader reqId s.leaderHint])
  else
    let e : Entry := { term := s.currentTerm, cmd := cmd, reqId := reqId }
    let lg := LogStore.append s.log e
    let idx := LogStore.lastIndex lg
    let s := { s with log := lg, pending := (idx, reqId) :: s.pending }
    -- A single-node cluster commits immediately; otherwise wait for a quorum.
    let ac := applyCommitted (advanceCommit s)
    (ac.1, broadcastAppend ac.1 ++ ac.2)

/-! ## The transition function -/

/--
**The Raft node.** Deterministic, total, and free of effects.

Every theorem in `RaftKV.Proof` is a statement about this function.
-/
def step (s : NodeState σ κ) : Event → NodeState σ κ × List Action
  | .recv src (.requestVote term candId lastIdx lastTerm) =>
      handleRequestVote s src term candId lastIdx lastTerm
  | .recv src (.requestVoteResp term granted) =>
      handleRequestVoteResp s term granted src
  | .recv src (.appendEntries term leaderId prevIdx prevTerm entries leaderCommit) =>
      handleAppendEntries s src term leaderId prevIdx prevTerm entries leaderCommit
  | .recv src (.appendEntriesResp term success matchIdx) =>
      handleAppendEntriesResp s src term success matchIdx
  | .recv _ (.installSnapshot term leaderId lastIdx anchor pairs) =>
      handleInstallSnapshot s term leaderId lastIdx anchor pairs
  | .clientReq reqId cmd => handleClientReq s reqId cmd
  | .electionTimeout =>
      if s.role == .leader then (s, []) else startElection s
  | .heartbeatTimeout =>
      if s.role == .leader then (s, broadcastAppend s) else (s, [])

end RaftKV.Protocol
