import RaftKV.Protocol.Node

/-!
# The adversarial network model

The whole distributed system as a transition relation. This is proof-level
only: nothing here is executed.

The network is modelled by a list `sent` of every packet ever transmitted,
which is only ever **appended to**. Delivery picks *any* element of that list.
This single choice gives us, for free, every failure mode a real network has:

* **loss** — a packet is simply never chosen;
* **reordering** — packets may be chosen in any order;
* **duplication** — a packet may be chosen any number of times.

A consequence worth stating plainly: because the model already permits
arbitrary loss, reordering and duplication, *any* real transport is a
refinement of it. Replacing the connection-per-message TCP transport with a
pooled, pipelined, batched one cannot invalidate a single theorem below.
-/

namespace RaftKV.Protocol

open RaftKV

variable {σ κ : Type} [LogStore σ] [KVStore κ]

/-- A packet in flight: sender, recipient, payload. -/
abbrev Packet := Nat × Nat × Msg

/--
Ghost: one client-visible event, stamped with the step at which it happened.

`time` is the value of the world's step counter, so it is a real-time clock in
the only sense the model has one: the steps of the system are totally ordered,
and `time` is that order. "A's response happened before B's invocation" is
`respond`'s `time` being strictly less than `invoke`'s.
-/
inductive HEvent where
  /-- A client submitted `cmd` to node `node` under request id `rid`. -/
  | invoke (time node rid : Nat) (cmd : Command)
  /-- Node `node` answered request `rid` with `r`, at log index `idx`. -/
  | respond (time node rid idx : Nat) (r : Reply)
  deriving Repr, DecidableEq, Inhabited

/--
A global state: every replica, everything ever sent, and a **ghost** record of
every vote ever cast.

`votes` is proof-only instrumentation. It never appears in `step`, so the
executable path is completely unaffected by it. It exists because a node's
*self*-vote lives in `votedFor` and is never transmitted, so `sent` alone cannot
witness it. Without that record, "at most one node ever wins term `t`" — the
anchor every log-level safety property needs — is not expressible, because a
current-state invariant says nothing once the term-`t` leader has died.
-/
structure World (σ κ : Type) where
  /-- Replica states indexed by node id. -/
  nodes : Nat → NodeState σ κ
  /-- Every packet ever transmitted. Grows monotonically. -/
  sent : List Packet
  /-- Ghost: every `(voter, candidate, term)` vote ever cast. Grows monotonically. -/
  votes : List (Nat × Nat × Nat)
  /-- Ghost: every `(node, term)` pair for which the node has held leadership. -/
  led : List (Nat × Nat)
  /-- Ghost: every `(creator, index, entry)` a leader has minted for a client. -/
  created : List (Nat × Nat × Entry)
  /-- Ghost: for each minted entry, `(index, entry, term of the entry beneath it)`. -/
  chain : List (Nat × Entry × Nat)
  /-- Ghost: `(node, term, log)` captured at the moment a node assumes leadership. -/
  elected : List (Nat × Nat × σ)
  /-- Ghost: `(leader, term, index, log, quorum)` recorded when a leader advances its commit index. -/
  commits : List (Nat × Nat × Nat × σ × List Nat)
  /-- Ghost: `(acker, term, matchIndex, log)` snapshots taken when a follower acks. -/
  acks : List (Nat × Nat × Nat × σ)
  /-- Ghost: `(voter, term, log)` snapshots taken when a node grants a vote. -/
  voteLogs : List (Nat × Nat × σ)
  /-- Ghost: `(node, term, log)` snapshot taken at every step at which a node leads. -/
  leaderLogs : List (Nat × Nat × σ)
  /-- Ghost: the number of steps taken so far — the model's clock. -/
  clock : Nat
  /-- Ghost: the client-visible history, in real-time (that is, step) order. -/
  hist : List HEvent
  /--
  Ghost: each node's log **as it would be had nothing ever been compacted**.

  Compaction discards a prefix, so a node's own log stops being able to answer
  questions about low indices — and every safety invariant here is a claim about
  what logs hold. Rather than weaken each of those claims with a window
  condition (which makes some of them outright false, since two recorded logs
  can have discarded different amounts), the invariants are stated about this
  ghost log, which never discards anything. One bridge invariant relates it to
  what a node actually holds, and that is the entire cost of compaction to the
  proofs.

  This is ghost state on the `World`, which the running system never builds, so
  it costs the implementation nothing.
  -/
  full : Nat → σ
  /-- Ghost: `(entry, time)` for every entry a leader has minted. -/
  createTime : List (Entry × Nat)
  /-- Ghost: `(committed index, the log committed against, time)` for every commit. -/
  commitTime : List (Nat × σ × Nat)

/-- The packets a node's actions put on the network. -/
def sendsOf (i : Nat) (acts : List Action) : List Packet :=
  acts.filterMap (fun a => match a with | .send to m => some (i, to, m) | _ => none)

/-- Ghost: the leadership `i` holds in state `s`, if any. -/
def ledOf (i : Nat) (s : NodeState σ κ) : List (Nat × Nat) :=
  if s.role = Role.leader then [(i, s.currentTerm)] else []

/--
Ghost: how the logical log evolves — the same operation the node performs on its
own log, applied to a log that has never discarded anything.

The three cases mirror `RaftKV.Proof.step_log`: a client request appends, an
accepted `AppendEntries` splices, and nothing else touches the log.
`aeAccepts` is the very condition `handleAppendEntries` branches on, so the two
cannot drift.
-/
def fullStep (s : NodeState σ κ) (fl : σ) (ev : Event) : σ :=
  match ev with
  | .clientReq rid cmd =>
      if s.role = Role.leader then
        LogStore.append fl { term := s.currentTerm, cmd := cmd, reqId := rid }
      else fl
  | .recv _ (.appendEntries term _ prevIdx prevTerm es _) =>
      if Protocol.aeAccepts s term prevIdx prevTerm then appendFrom fl (prevIdx + 1) es else fl
  | _ => fl

/-- Ghost: the entry node `i` mints while handling `ev`, if any. -/
def createdOf (i : Nat) (s : NodeState σ κ) (fl : σ) (ev : Event) : List (Nat × Nat × Entry) :=
  match ev with
  | .clientReq rid cmd =>
      if s.role = Role.leader then
        [(i, LogStore.lastIndex fl, { term := s.currentTerm, cmd := cmd, reqId := rid })]
      else []
  | _ => []

/--
Ghost: the predecessor link for the entry `i` mints while handling `ev`.

Records the term of the entry directly beneath the new one. Since an entry is
determined by its index and term, this term pins down the entry beneath it, and
chasing the links downwards is what proves two agreeing logs agree all the way
to the start.
-/
def chainOf (i : Nat) (s : NodeState σ κ) (fl : σ) (ev : Event) : List (Nat × Entry × Nat) :=
  match ev with
  | .clientReq rid cmd =>
      if s.role = Role.leader then
        [(LogStore.lastIndex fl, { term := s.currentTerm, cmd := cmd, reqId := rid },
          (LogStore.termAt fl (LogStore.lastIndex fl - 1)).getD 0)]
      else []
  | _ => []

/--
Ghost: the log `i` holds at the instant it assumes leadership.

Leader Completeness is a claim about the log a leader had *when it was elected*,
which no current-state predicate can express once that leader has moved on. The
log is stored as a `σ` value rather than a list, so this needs no lawfulness
instance and leaves the executable path untouched.
-/
def electedOf (i : Nat) (pre post : NodeState σ κ) (fl : σ) : List (Nat × Nat × σ) :=
  if post.role = Role.leader ∧ pre.role ≠ Role.leader then
    [(i, post.currentTerm, fl)]
  else []

/--
Ghost: a leader's commit decision, snapshotted with the log it committed against
and the quorum it counted.

Recorded only when the index genuinely *advances* under leadership. A leader's
`commitIndex` can also be inherited from its time as a follower, and such an
index is not justified by this leader's own `matchIndex` — it was justified by
an earlier leader, which has its own record.
-/
def commitOf (i : Nat) (pre post : NodeState σ κ) (fl : σ) :
    List (Nat × Nat × Nat × σ × List Nat) :=
  if post.role = Role.leader ∧ pre.commitIndex < post.commitIndex then
    [(i, post.currentTerm, post.commitIndex, fl, replicatedOn post post.commitIndex)]
  else []

/--
Ghost: a follower's acknowledgement, snapshotted with the log it acknowledged.

`Committed` has to mean "a quorum held this entry *at some point*", which no
current-state predicate can express, since a follower may later be overwritten
by a different leader. Recording the acking log makes the quorum's contents
permanent evidence.
-/
def ackOf (i : Nat) (s : NodeState σ κ) (fl : σ) (acts : List Action) :
    List (Nat × Nat × Nat × σ) :=
  acts.filterMap (fun a =>
    match a with
    | .send _ (.appendEntriesResp t true m) => some (i, t, m, fl)
    | _ => none)
  ++ (if s.role = Role.leader then [(i, s.currentTerm, LogStore.lastIndex fl, fl)] else [])

/--
Ghost: the log a voter held when it granted a vote.

The `upToDate` check compares the candidate's advertised log against the
*voter's log at that instant*, so that log has to be on record for the check to
mean anything later.
-/
def voteLogOf (i : Nat) (s : NodeState σ κ) (fl : σ) (acts : List Action) :
    List (Nat × Nat × σ) :=
  acts.filterMap (fun a =>
    match a with
    | .send _ (.requestVoteResp t true) => some (i, t, fl)
    | _ => none)

/--
Ghost: a leader's log, snapshotted at every step at which it leads.

Leader Completeness has to talk about *the* term-`t` leader's log — an object
that outlives the leader. Since a leader's log only grows while it leads
(`leader_log_monotone`) and it cannot be demoted within its term
(`leader_stable`), the snapshots for a given `(node, term)` form a chain under
prefix, and any one of them can stand for "what that leader had".
-/
def leaderLogOf (i : Nat) (s : NodeState σ κ) (fl : σ) : List (Nat × Nat × σ) :=
  if s.role = Role.leader then [(i, s.currentTerm, fl)] else []

/-- Ghost: the vote node `i` holds in state `s`, if any. -/
def voteOf (i : Nat) (s : NodeState σ κ) : List (Nat × Nat × Nat) :=
  match s.votedFor with
  | some c => [(i, c, s.currentTerm)]
  | none => []

/--
Ghost: the client-visible events node `i` produces in this step, at time `t`.

An `Event.clientReq` is the invocation; each `Action.reply` is a response,
carrying the log index at which the command took effect.
-/
def histOf (i : Nat) (ev : Event) (acts : List Action) (t : Nat) : List HEvent :=
  (match ev with
    | .clientReq rid cmd => [HEvent.invoke t i rid cmd]
    | .recv _ _ => []
    | .electionTimeout => []
    | .heartbeatTimeout => [])
  ++ acts.filterMap (fun a =>
      match a with
      | .reply idx rid r => some (HEvent.respond t i rid idx r)
      | _ => none)

/-- Ghost: when each minted entry was minted. -/
def createTimeOf (i : Nat) (s : NodeState σ κ) (fl : σ) (ev : Event) (t : Nat) :
    List (Entry × Nat) :=
  (createdOf i s fl ev).map (fun r => (r.2.2, t))

/-- Ghost: when each commit happened, and against which log. -/
def commitTimeOf (i : Nat) (pre post : NodeState σ κ) (fl : σ) (t : Nat) :
    List (Nat × σ × Nat) :=
  (commitOf i pre post fl).map (fun r => (r.2.2.1, r.2.2.2.1, t))

/-- Deliver `ev` to node `i`, recording whatever it transmits and votes. -/
def World.act (w : World σ κ) (i : Nat) (ev : Event) : World σ κ :=
  let (s', acts) := Protocol.step (w.nodes i) ev
  let fl := fullStep (w.nodes i) (w.full i) ev
  { nodes := fun j => if j = i then s' else w.nodes j,
    full := fun j => if j = i then fl else w.full j,
    sent := w.sent ++ sendsOf i acts,
    votes := w.votes ++ voteOf i s',
    led := w.led ++ ledOf i s',
    created := w.created ++ createdOf i s' fl ev,
    chain := w.chain ++ chainOf i s' fl ev,
    elected := w.elected ++ electedOf i (w.nodes i) s' fl,
    commits := w.commits ++ commitOf i (w.nodes i) s' fl,
    acks := w.acks ++ ackOf i s' fl acts,
    voteLogs := w.voteLogs ++ voteLogOf i s' fl acts,
    leaderLogs := w.leaderLogs ++ leaderLogOf i s' fl,
    clock := w.clock + 1,
    hist := w.hist ++ histOf i ev acts w.clock,
    createTime := w.createTime ++ createTimeOf i s' fl ev w.clock,
    commitTime := w.commitTime ++ commitTimeOf i (w.nodes i) s' fl w.clock }

/--
Node `i` crashes and restarts.

Volatile state is lost and the durable trio survives, exactly as
`Protocol.restart` says. No ghost list moves: a crash transmits nothing, votes
for no one, commits nothing and answers no client — it only forgets. Messages
already in flight are untouched, because the network model already permits any
packet never to be delivered.
-/
def World.crash (w : World σ κ) (i : Nat) : World σ κ :=
  { w with nodes := fun j => if j = i then Protocol.restart (w.nodes i) else w.nodes j,
           clock := w.clock + 1 }

/--
Node `i` compacts its log.

Nothing observable changes: no message is sent, no ghost record is written, and
the logical log — which every safety invariant is stated over — is untouched.
What changes is only how much of it the node still holds.
-/
def World.compactAt (w : World σ κ) (i : Nat) : World σ κ :=
  { w with nodes := fun j => if j = i then Protocol.compactTo (w.nodes i) else w.nodes j,
           clock := w.clock + 1 }

/-- The starting state: every node freshly initialised, nothing sent or voted. -/
def World.init (members : List Nat) : World σ κ :=
  { nodes := fun i => Protocol.initState { me := i, members := members },
    sent := [], votes := [], led := [], created := [], chain := [], elected := [],
    commits := [], acks := [], voteLogs := [], leaderLogs := [],
    clock := 0, hist := [], full := fun _ => LogStore.empty,
    createTime := [], commitTime := [] }

/--
One step of the system. Only cluster members run the protocol.

Note there is no "drop", "reorder" or "duplicate" rule: those are consequences
of `deliver` being free to choose any previously sent packet, and of `sent`
never shrinking.
-/
inductive Step (members : List Nat) : World σ κ → World σ κ → Prop where
  /-- Any previously sent packet may be delivered, at any time, any number of times. -/
  | deliver (w : World σ κ) (src dst : Nat) (m : Msg) :
      dst ∈ members → (src, dst, m) ∈ w.sent → Step members w (w.act dst (.recv src m))
  /-- Any node may decide its election timer expired. -/
  | electionTimeout (w : World σ κ) (i : Nat) :
      i ∈ members → Step members w (w.act i .electionTimeout)
  /-- Any node may decide its heartbeat timer expired. -/
  | heartbeat (w : World σ κ) (i : Nat) :
      i ∈ members → Step members w (w.act i .heartbeatTimeout)
  /-- A client may submit a command to any node. -/
  | client (w : World σ κ) (i rid : Nat) (cmd : Command) :
      i ∈ members → Step members w (w.act i (.clientReq rid cmd))
  /-- Any node may crash and restart, losing everything but its durable state. -/
  | crash (w : World σ κ) (i : Nat) :
      i ∈ members → Step members w (w.crash i)
  /-- Any node may compact its log, discarding what its snapshot now covers. -/
  | compact (w : World σ κ) (i : Nat) :
      i ∈ members → Step members w (w.compactAt i)

/-! ### Reading a crashed world -/

@[simp] theorem crash_nodes_self (w : World σ κ) (i : Nat) :
    (w.crash i).nodes i = Protocol.restart (w.nodes i) := by
  rw [World.crash]; dsimp only; rw [if_pos rfl]

@[simp] theorem crash_nodes_ne (w : World σ κ) (i : Nat) {j : Nat} (h : j ≠ i) :
    (w.crash i).nodes j = w.nodes j := by
  rw [World.crash]; dsimp only; rw [if_neg h]

@[simp] theorem crash_sent (w : World σ κ) (i : Nat) : (w.crash i).sent = w.sent := rfl
@[simp] theorem crash_votes (w : World σ κ) (i : Nat) : (w.crash i).votes = w.votes := rfl
@[simp] theorem crash_led (w : World σ κ) (i : Nat) : (w.crash i).led = w.led := rfl
@[simp] theorem crash_created (w : World σ κ) (i : Nat) : (w.crash i).created = w.created := rfl
@[simp] theorem crash_chain (w : World σ κ) (i : Nat) : (w.crash i).chain = w.chain := rfl
@[simp] theorem crash_elected (w : World σ κ) (i : Nat) : (w.crash i).elected = w.elected := rfl
@[simp] theorem crash_commits (w : World σ κ) (i : Nat) : (w.crash i).commits = w.commits := rfl
@[simp] theorem crash_acks (w : World σ κ) (i : Nat) : (w.crash i).acks = w.acks := rfl
@[simp] theorem crash_voteLogs (w : World σ κ) (i : Nat) :
    (w.crash i).voteLogs = w.voteLogs := rfl
@[simp] theorem crash_leaderLogs (w : World σ κ) (i : Nat) :
    (w.crash i).leaderLogs = w.leaderLogs := rfl
@[simp] theorem crash_hist (w : World σ κ) (i : Nat) : (w.crash i).hist = w.hist := rfl
@[simp] theorem crash_createTime (w : World σ κ) (i : Nat) :
    (w.crash i).createTime = w.createTime := rfl
@[simp] theorem crash_commitTime (w : World σ κ) (i : Nat) :
    (w.crash i).commitTime = w.commitTime := rfl
@[simp] theorem crash_clock (w : World σ κ) (i : Nat) : (w.crash i).clock = w.clock + 1 := rfl

/-! ### Compaction moves nothing but one node's log -/

@[simp] theorem compactAt_nodes_self (w : World σ κ) (i : Nat) :
    (w.compactAt i).nodes i = Protocol.compactTo (w.nodes i) := by
  rw [World.compactAt]; dsimp only; rw [if_pos rfl]
@[simp] theorem compactAt_nodes_ne (w : World σ κ) (i : Nat) {j : Nat} (h : j ≠ i) :
    (w.compactAt i).nodes j = w.nodes j := by
  rw [World.compactAt]; dsimp only; rw [if_neg h]
@[simp] theorem compactAt_full (w : World σ κ) (i : Nat) : (w.compactAt i).full = w.full := rfl
@[simp] theorem compactAt_sent (w : World σ κ) (i : Nat) : (w.compactAt i).sent = w.sent := rfl
@[simp] theorem compactAt_votes (w : World σ κ) (i : Nat) : (w.compactAt i).votes = w.votes := rfl
@[simp] theorem compactAt_led (w : World σ κ) (i : Nat) : (w.compactAt i).led = w.led := rfl
@[simp] theorem compactAt_created (w : World σ κ) (i : Nat) :
    (w.compactAt i).created = w.created := rfl
@[simp] theorem compactAt_chain (w : World σ κ) (i : Nat) : (w.compactAt i).chain = w.chain := rfl
@[simp] theorem compactAt_elected (w : World σ κ) (i : Nat) :
    (w.compactAt i).elected = w.elected := rfl
@[simp] theorem compactAt_commits (w : World σ κ) (i : Nat) :
    (w.compactAt i).commits = w.commits := rfl
@[simp] theorem compactAt_acks (w : World σ κ) (i : Nat) : (w.compactAt i).acks = w.acks := rfl
@[simp] theorem compactAt_voteLogs (w : World σ κ) (i : Nat) :
    (w.compactAt i).voteLogs = w.voteLogs := rfl
@[simp] theorem compactAt_leaderLogs (w : World σ κ) (i : Nat) :
    (w.compactAt i).leaderLogs = w.leaderLogs := rfl
@[simp] theorem compactAt_hist (w : World σ κ) (i : Nat) : (w.compactAt i).hist = w.hist := rfl
@[simp] theorem compactAt_createTime (w : World σ κ) (i : Nat) :
    (w.compactAt i).createTime = w.createTime := rfl
@[simp] theorem compactAt_commitTime (w : World σ κ) (i : Nat) :
    (w.compactAt i).commitTime = w.commitTime := rfl
@[simp] theorem compactAt_clock (w : World σ κ) (i : Nat) :
    (w.compactAt i).clock = w.clock + 1 := rfl

/-- Compaction leaves every field but the log and the snapshot alone. -/
@[simp] theorem compactTo_currentTerm (s : NodeState σ κ) :
    (Protocol.compactTo s).currentTerm = s.currentTerm := by
  rw [Protocol.compactTo]; split <;> rfl
@[simp] theorem compactTo_votedFor (s : NodeState σ κ) :
    (Protocol.compactTo s).votedFor = s.votedFor := by
  rw [Protocol.compactTo]; split <;> rfl
@[simp] theorem compactTo_role (s : NodeState σ κ) :
    (Protocol.compactTo s).role = s.role := by
  rw [Protocol.compactTo]; split <;> rfl
@[simp] theorem compactTo_commitIndex (s : NodeState σ κ) :
    (Protocol.compactTo s).commitIndex = s.commitIndex := by
  rw [Protocol.compactTo]; split <;> rfl
@[simp] theorem compactTo_lastApplied (s : NodeState σ κ) :
    (Protocol.compactTo s).lastApplied = s.lastApplied := by
  rw [Protocol.compactTo]; split <;> rfl
@[simp] theorem compactTo_kv (s : NodeState σ κ) :
    (Protocol.compactTo s).kv = s.kv := by
  rw [Protocol.compactTo]; split <;> rfl
@[simp] theorem compactTo_cfg (s : NodeState σ κ) :
    (Protocol.compactTo s).cfg = s.cfg := by
  rw [Protocol.compactTo]; split <;> rfl
@[simp] theorem compactTo_votesGranted (s : NodeState σ κ) :
    (Protocol.compactTo s).votesGranted = s.votesGranted := by
  rw [Protocol.compactTo]; split <;> rfl
@[simp] theorem compactTo_nextIndex (s : NodeState σ κ) :
    (Protocol.compactTo s).nextIndex = s.nextIndex := by
  rw [Protocol.compactTo]; split <;> rfl
@[simp] theorem compactTo_matchIndex (s : NodeState σ κ) :
    (Protocol.compactTo s).matchIndex = s.matchIndex := by
  rw [Protocol.compactTo]; split <;> rfl
@[simp] theorem compactTo_pending (s : NodeState σ κ) :
    (Protocol.compactTo s).pending = s.pending := by
  rw [Protocol.compactTo]; split <;> rfl
@[simp] theorem compactTo_leaderHint (s : NodeState σ κ) :
    (Protocol.compactTo s).leaderHint = s.leaderHint := by
  rw [Protocol.compactTo]; split <;> rfl

/-- A restart keeps the durable trio and forgets the rest. -/
@[simp] theorem restart_currentTerm (s : NodeState σ κ) :
    (Protocol.restart s).currentTerm = s.currentTerm := rfl
@[simp] theorem restart_votedFor (s : NodeState σ κ) :
    (Protocol.restart s).votedFor = s.votedFor := rfl
@[simp] theorem restart_log (s : NodeState σ κ) : (Protocol.restart s).log = s.log := rfl
@[simp] theorem restart_cfg (s : NodeState σ κ) : (Protocol.restart s).cfg = s.cfg := rfl
@[simp] theorem restart_role (s : NodeState σ κ) :
    (Protocol.restart s).role = Role.follower := rfl
@[simp] theorem restart_commitIndex (s : NodeState σ κ) :
    (Protocol.restart s).commitIndex = s.snapIndex := rfl
@[simp] theorem restart_lastApplied (s : NodeState σ κ) :
    (Protocol.restart s).lastApplied = s.snapIndex := rfl
@[simp] theorem restart_snapIndex (s : NodeState σ κ) :
    (Protocol.restart s).snapIndex = s.snapIndex := rfl
@[simp] theorem restart_snapKV (s : NodeState σ κ) :
    (Protocol.restart s).snapKV = (KVStore.ofPairs (KVStore.toPairs s.snapKV) : κ) := rfl
@[simp] theorem restart_votesGranted (s : NodeState σ κ) :
    (Protocol.restart s).votesGranted = [] := rfl
@[simp] theorem restart_pending (s : NodeState σ κ) : (Protocol.restart s).pending = [] := rfl
@[simp] theorem restart_kv (s : NodeState σ κ) :
    (Protocol.restart s).kv = (KVStore.ofPairs (KVStore.toPairs s.snapKV) : κ) := rfl

/-- Nor across a compaction, which touches only the log. -/
theorem compact_term_mono (w : World σ κ) (i j : Nat) :
    (w.nodes j).currentTerm ≤ ((w.compactAt i).nodes j).currentTerm := by
  by_cases h : j = i
  · subst h; rw [compactAt_nodes_self, compactTo_currentTerm]; exact Nat.le_refl _
  · rw [compactAt_nodes_ne _ _ h]; exact Nat.le_refl _

/-- A node's term never moves backwards across a crash either. -/
theorem crash_term_mono (w : World σ κ) (i j : Nat) :
    (w.nodes j).currentTerm ≤ ((w.crash i).nodes j).currentTerm := by
  by_cases h : j = i
  · subst h; rw [crash_nodes_self, restart_currentTerm]; exact Nat.le_refl _
  · rw [crash_nodes_ne _ _ h]; exact Nat.le_refl _

/-- Worlds arising from the initial state by finitely many steps. -/
inductive Reachable (members : List Nat) : World σ κ → Prop where
  /-- The initial world is reachable. -/
  | init : Reachable members (World.init members)
  /-- Reachability is closed under `Step`. -/
  | tail {w w' : World σ κ} : Reachable members w → Step members w w' → Reachable members w'

/-! ## Commitment

An entry is **committed** when some leader's commit index has reached it, with
that leader's own log holding the entry there. The snapshot makes the claim
permanent: it stays true of the reachable world even after the leader has died
and other replicas have moved on.
-/

/-- Entry `e` at index `idx` was committed by a term-`T` leader. -/
def Committed (w : World σ κ) (idx : Nat) (e : Entry) (T : Nat) : Prop :=
  ∃ L c lg Q, (L, T, c, lg, Q) ∈ w.commits ∧ idx ≤ c ∧ LogStore.get lg idx = some e

/--
**Leader Completeness.** An entry committed in term `T` is present, at the same
index, in the log of every leader elected in a later term.
-/
def LeaderCompleteness (w : World σ κ) : Prop :=
  ∀ idx e T U L lg, Committed w idx e T → (L, U, lg) ∈ w.elected → T < U →
    LogStore.get lg idx = some e

/-! ## The safety properties

Stated here so that the statements are readable independently of their proofs.
-/

/-- Node `i` currently believes it leads term `t`. -/
def IsLeaderIn (w : World σ κ) (i t : Nat) : Prop :=
  (w.nodes i).role = Role.leader ∧ (w.nodes i).currentTerm = t

/--
**Election Safety.** At most one node leads any given term.
-/
def ElectionSafety (w : World σ κ) : Prop :=
  ∀ i j t, IsLeaderIn w i t → IsLeaderIn w j t → i = j

/--
**Log Matching.** If two logs hold an entry with the same index and term, they
agree on every entry up to that index.
-/
def LogMatching [LawfulLogStore σ] (w : World σ κ) : Prop :=
  ∀ i j idx e₁ e₂,
    LogStore.get (w.full i) idx = some e₁ →
    LogStore.get (w.full j) idx = some e₂ →
    e₁.term = e₂.term →
    ∀ k ≤ idx, LogStore.get (w.full i) k = LogStore.get (w.full j) k

/-! ### The client-visible history -/

/-- A client submitted request `rid` at time `t`. -/
def Submitted (w : World σ κ) (t rid : Nat) : Prop :=
  ∃ (i : Nat) (cmd : Command), HEvent.invoke t i rid cmd ∈ w.hist

/-- The cluster answered request `rid` with `r` at time `t`, at log index `n`. -/
def Answered (w : World σ κ) (t rid n : Nat) (r : Reply) : Prop :=
  ∃ i, HEvent.respond t i rid n r ∈ w.hist

/--
Clients never reuse a request id.

This is the client's side of the contract, and it is what makes "the operation
for `rid`" a well-defined thing to talk about.
-/
def FreshIds (w : World σ κ) : Prop :=
  ∀ t₁ t₂ rid, Submitted w t₁ rid → Submitted w t₂ rid → t₁ = t₂

/--
**State Machine Safety.** Two nodes never apply different entries at the same
log index.
-/
def StateMachineSafety [LawfulLogStore σ] (w : World σ κ) : Prop :=
  ∀ i j idx e₁ e₂,
    idx ≤ (w.nodes i).lastApplied →
    idx ≤ (w.nodes j).lastApplied →
    LogStore.get (w.full i) idx = some e₁ →
    LogStore.get (w.full j) idx = some e₂ →
    e₁ = e₂

end RaftKV.Protocol
