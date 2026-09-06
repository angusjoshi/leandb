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

/-- The packets a node's actions put on the network. -/
def sendsOf (i : Nat) (acts : List Action) : List Packet :=
  acts.filterMap (fun a => match a with | .send to m => some (i, to, m) | _ => none)

/-- Ghost: the leadership `i` holds in state `s`, if any. -/
def ledOf (i : Nat) (s : NodeState σ κ) : List (Nat × Nat) :=
  if s.role = Role.leader then [(i, s.currentTerm)] else []

/-- Ghost: the entry node `i` mints while handling `ev`, if any. -/
def createdOf (i : Nat) (s : NodeState σ κ) (ev : Event) : List (Nat × Nat × Entry) :=
  match ev with
  | .clientReq rid cmd =>
      if s.role = Role.leader then
        [(i, LogStore.lastIndex s.log, { term := s.currentTerm, cmd := cmd, reqId := rid })]
      else []
  | _ => []

/--
Ghost: the predecessor link for the entry `i` mints while handling `ev`.

Records the term of the entry directly beneath the new one. Since an entry is
determined by its index and term, this term pins down the entry beneath it, and
chasing the links downwards is what proves two agreeing logs agree all the way
to the start.
-/
def chainOf (i : Nat) (s : NodeState σ κ) (ev : Event) : List (Nat × Entry × Nat) :=
  match ev with
  | .clientReq rid cmd =>
      if s.role = Role.leader then
        [(LogStore.lastIndex s.log, { term := s.currentTerm, cmd := cmd, reqId := rid },
          (LogStore.termAt s.log (LogStore.lastIndex s.log - 1)).getD 0)]
      else []
  | _ => []

/--
Ghost: the log `i` holds at the instant it assumes leadership.

Leader Completeness is a claim about the log a leader had *when it was elected*,
which no current-state predicate can express once that leader has moved on. The
log is stored as a `σ` value rather than a list, so this needs no lawfulness
instance and leaves the executable path untouched.
-/
def electedOf (i : Nat) (pre post : NodeState σ κ) : List (Nat × Nat × σ) :=
  if post.role = Role.leader ∧ pre.role ≠ Role.leader then
    [(i, post.currentTerm, post.log)]
  else []

/--
Ghost: a leader's commit decision, snapshotted with the log it committed against
and the quorum it counted.

Recorded only when the index genuinely *advances* under leadership. A leader's
`commitIndex` can also be inherited from its time as a follower, and such an
index is not justified by this leader's own `matchIndex` — it was justified by
an earlier leader, which has its own record.
-/
def commitOf (i : Nat) (pre post : NodeState σ κ) : List (Nat × Nat × Nat × σ × List Nat) :=
  if post.role = Role.leader ∧ pre.commitIndex < post.commitIndex then
    [(i, post.currentTerm, post.commitIndex, post.log, replicatedOn post post.commitIndex)]
  else []

/--
Ghost: a follower's acknowledgement, snapshotted with the log it acknowledged.

`Committed` has to mean "a quorum held this entry *at some point*", which no
current-state predicate can express, since a follower may later be overwritten
by a different leader. Recording the acking log makes the quorum's contents
permanent evidence.
-/
def ackOf (i : Nat) (s : NodeState σ κ) (acts : List Action) : List (Nat × Nat × Nat × σ) :=
  acts.filterMap (fun a =>
    match a with
    | .send _ (.appendEntriesResp t true m) => some (i, t, m, s.log)
    | _ => none)
  ++ (if s.role = Role.leader then [(i, s.currentTerm, LogStore.lastIndex s.log, s.log)] else [])

/--
Ghost: the log a voter held when it granted a vote.

The `upToDate` check compares the candidate's advertised log against the
*voter's log at that instant*, so that log has to be on record for the check to
mean anything later.
-/
def voteLogOf (i : Nat) (s : NodeState σ κ) (acts : List Action) : List (Nat × Nat × σ) :=
  acts.filterMap (fun a =>
    match a with
    | .send _ (.requestVoteResp t true) => some (i, t, s.log)
    | _ => none)

/--
Ghost: a leader's log, snapshotted at every step at which it leads.

Leader Completeness has to talk about *the* term-`t` leader's log — an object
that outlives the leader. Since a leader's log only grows while it leads
(`leader_log_monotone`) and it cannot be demoted within its term
(`leader_stable`), the snapshots for a given `(node, term)` form a chain under
prefix, and any one of them can stand for "what that leader had".
-/
def leaderLogOf (i : Nat) (s : NodeState σ κ) : List (Nat × Nat × σ) :=
  if s.role = Role.leader then [(i, s.currentTerm, s.log)] else []

/-- Ghost: the vote node `i` holds in state `s`, if any. -/
def voteOf (i : Nat) (s : NodeState σ κ) : List (Nat × Nat × Nat) :=
  match s.votedFor with
  | some c => [(i, c, s.currentTerm)]
  | none => []

/-- Deliver `ev` to node `i`, recording whatever it transmits and votes. -/
def World.act (w : World σ κ) (i : Nat) (ev : Event) : World σ κ :=
  let (s', acts) := Protocol.step (w.nodes i) ev
  { nodes := fun j => if j = i then s' else w.nodes j,
    sent := w.sent ++ sendsOf i acts,
    votes := w.votes ++ voteOf i s',
    led := w.led ++ ledOf i s',
    created := w.created ++ createdOf i s' ev,
    chain := w.chain ++ chainOf i s' ev,
    elected := w.elected ++ electedOf i (w.nodes i) s',
    commits := w.commits ++ commitOf i (w.nodes i) s',
    acks := w.acks ++ ackOf i s' acts,
    voteLogs := w.voteLogs ++ voteLogOf i s' acts,
    leaderLogs := w.leaderLogs ++ leaderLogOf i s' }

/-- The starting state: every node freshly initialised, nothing sent or voted. -/
def World.init (members : List Nat) : World σ κ :=
  { nodes := fun i => Protocol.initState { me := i, members := members },
    sent := [], votes := [], led := [], created := [], chain := [], elected := [],
    commits := [], acks := [], voteLogs := [], leaderLogs := [] }

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
    LogStore.get (w.nodes i).log idx = some e₁ →
    LogStore.get (w.nodes j).log idx = some e₂ →
    e₁.term = e₂.term →
    ∀ k ≤ idx, LogStore.get (w.nodes i).log k = LogStore.get (w.nodes j).log k

/--
**State Machine Safety.** Two nodes never apply different entries at the same
log index.
-/
def StateMachineSafety [LawfulLogStore σ] (w : World σ κ) : Prop :=
  ∀ i j idx e₁ e₂,
    idx ≤ (w.nodes i).lastApplied →
    idx ≤ (w.nodes j).lastApplied →
    LogStore.get (w.nodes i).log idx = some e₁ →
    LogStore.get (w.nodes j).log idx = some e₂ →
    e₁ = e₂

end RaftKV.Protocol
