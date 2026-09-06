# Verification status

This file states precisely what is proved, what is assumed, and what is not
done. Nothing below is aspirational: every "proved" item is a `sorry`-free Lean
theorem in this repository, depending only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`), which you can confirm yourself:

```
lake env lean -- <<'X'
import RaftKV
#print axioms RaftKV.Proof.leaderCompleteness
#print axioms RaftKV.Proof.stateMachineSafety
X
```

**Status: all four of Raft's safety properties are proved**, and the refinement
chain from the sequential key/value specification down to the replicas'
observable state is closed (`Proof.replicas_agree`). See below.

## Proved

### Refinement of the abstractions
| Theorem | Statement |
|---|---|
| `LogStore.get_isSome_iff`, `get_append_of_le`, `get_append_self`, `get_truncFrom_of_lt`, `lastIndex_truncFrom_le` | The log interface's derived operations behave as the `List Entry` model says, for **every** lawful implementation |
| `ArrayLog` instances | The array-backed log satisfies all six `LawfulLogStore` laws |
| `KVStore.applyCmd_refines` | The executable state machine produces exactly the reply and the state the sequential spec demands |
| `KVStore.applyAll_refines` | ...and this extends to whole command sequences |
| `HashKV` instances | The hash-map state machine satisfies all four `LawfulKVStore` laws |

### Wire format
| Theorem | Statement |
|---|---|
| `Codec.decode_encode` (Command, Entry, Msg) | Decoding an encoding returns the original value and leaves the remaining input untouched |
| `decEntries_encEntries` | Length-prefixed entry lists round-trip |
| `Codec.encode_injective` | Distinct messages never share a wire form |

### Protocol
| Theorem | Statement |
|---|---|
| `Proof.quorum_intersect` | **Any two majorities of a cluster share a member** |
| `Proof.step_term_mono`, `world_term_mono` | A replica's `currentTerm` never decreases, under any event |
| `Proof.handle*_term_eq` | Each message handler leaves the term at exactly `max` of old term and message term |
| `Proof.step_cfg` | A replica's configuration is immutable |
| `Proof.votedFor_step` / `votedFor_stable` | **A vote, once cast, is never withdrawn within its term** |
| `Proof.step_requestVote_cid` | A `requestVote` always names its sender as the candidate |
| `Proof.grant_only_from_requestVote` | Only `handleRequestVote` can emit a vote grant |
| `Proof.handleRequestVote_grant` | A grant goes to the asker, carries the voter's post-event term, and is recorded in `votedFor` |
| `Proof.inv_reachable` | The four-part vote invariant holds in **every reachable world** |
| **`Proof.vote_uniqueness`** | **In every reachable world, no node ever grants two different term-`t` votes.** This is the deep result: it holds under arbitrary message loss, reordering, duplication, and interleaving. |
| `Proof.step_votes_char` | A node holding a non-follower role after an event either just started an election (tally = its own self-vote) or was already campaigning/leading with an unchanged term and a tally that at most gained one fresh grant |
| `Proof.step_leader_quorum` | Leadership is only ever *created* at a site that has just tested `isMajority` |
| `Proof.votes_act`, `fullInv_reachable` | The leader bookkeeping (`VotesInv` + `QuorumInv` + `SentFrom`) holds in every reachable world |
| **`Proof.electionSafety`** | **Election Safety — at most one node leads any given term, in every reachable world**, under arbitrary loss, reordering, duplication and interleaving |

Statement, as machine-checked:

```lean
theorem electionSafety {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (h : Reachable members w) : ElectionSafety w
-- where ElectionSafety w = ∀ i j t, IsLeaderIn w i t → IsLeaderIn w j t → i = j
```

### The durable election anchor (ghost vote history)
| Theorem | Statement |
|---|---|
| `Proof.gInv_step` | The ghost vote invariants are preserved by every step |
| `Proof.GInv.selfRec` | A node's currently held vote — **including its self-vote, which never travels on the wire** — is in the ghost history |
| `Proof.GVoteUnique` | One vote per node per term, self-votes included, for all time |
| `Proof.wonTerm_step` | Winning a term is permanent: the ghost history never shrinks |
| `Proof.wonTerm_of_leader` | A node that currently leads term `t` has won term `t` |
| **`Proof.everWinner_unique`** | **At most one node *ever* wins a given term** — unlike `electionSafety`, this survives the death of the leader in question |
| `Proof.leader_is_unique_winner` | A node leading term `t` is *the* unique winner of term `t` |
| `Proof.allInv_reachable` | All of the above hold in every reachable world |

`World.votes` is proof-only ghost state: it appears nowhere in `step`, and the
running system is byte-for-byte unaffected (re-verified end to end after it was
added).

### Log Matching, part one — entries are determined by (index, term)
| Theorem | Statement |
|---|---|
| `Proof.ledInv_reachable` | The leadership ghost record is sound in every reachable world |
| `Proof.led_unique` | **Leadership of a term is unique across all of history** |
| `Proof.led_not_leader_term_gt` | A node once recorded as leading term `t`, and not currently leading, has already moved past `t` |
| `Proof.cInv_reachable` | The created-entry invariants hold in every reachable world |
| **`Proof.entry_unique`** | **No two distinct entries are ever created at the same log index in the same term.** This is Raft's Log Matching Property, part one |

`World.led` and `World.created` are further proof-only ghost state. The argument:
a creator of a term-`t` entry is on record in `led` for `t`, and `led_unique`
says there is only ever one such node; that node's log still holds everything it
created while its term stands (`leader_stable` keeps it in office,
`leader_log_monotone` stops its log being rewritten); and a leader mints at
`lastIndex + 1`, beyond everything its log already holds, so it can never
collide with one of its own earlier entries.

### Log Matching, part one, on real logs
| Theorem | Statement |
|---|---|
| `LogStore.get_append`, `get_truncFrom`, `getElem?_sliceFrom` | Complete `get` equations for the log operations |
| `Proof.appendFrom_mem` | **Splicing preserves any per-entry property shared by the log and the payload** — the workhorse for the bridge |
| `Proof.step_log` | Complete description of how one step can change a node's log |
| `Proof.step_appendEntries_payload` | Every `appendEntries` a node emits is literally `appendEntriesTo` of its own post-state, so its payload is a tail of the sender's log |
| `Proof.bInv_reachable` | In every reachable world, every entry in any log **and** every entry in any payload on the wire was minted at that index |
| **`Proof.log_entry_unique`** | **If two replicas hold entries at the same log index with the same term, those entries are identical.** Raft's Log Matching Property, part one, on the actual replicated state |

### Log Matching, part two — agreeing logs agree all the way down
| Theorem | Statement |
|---|---|
| `Proof.chInv_reachable` | The predecessor-chain invariants hold in every reachable world |
| `Proof.ChainDet` | An index and entry determine the recorded predecessor term |
| `Proof.log_agree_pred` | Two logs agreeing at an index agree at the index below it |
| **`Proof.logMatching`** | **`Protocol.LogMatching` — if two replicas hold entries at the same index with the same term, their logs are identical at *every* index up to it** |

Statement, as machine-checked:

```lean
theorem logMatching (hnd : members.Nodup) (h : Reachable members w) : LogMatching w
-- LogMatching w = ∀ i j idx e₁ e₂,
--   get (w.nodes i).log idx = some e₁ → get (w.nodes j).log idx = some e₂ →
--   e₁.term = e₂.term → ∀ k ≤ idx, get (w.nodes i).log k = get (w.nodes j).log k
```

### Term bounds
| Theorem | Statement |
|---|---|
| `Proof.tInv_reachable` | No replica holds an entry stamped with a term it has not reached, and no replication payload carries entries from beyond the term it is sent in |
| `Proof.chainSorted_reachable` | A recorded predecessor term never exceeds the term of the entry above it |
| **`Proof.wf_terms_sorted`, `wf_sorted`** | **Log terms are non-decreasing** — in any well-formed log, an entry at a lower index never has a higher term |
| **`Proof.wf_le_lastTerm`** | **A log's last term bounds every term in it** — the form the `upToDate` comparison actually uses |

Sortedness is what lets a comparison of two logs' *last* terms say anything
about their contents at shared indices, which is precisely what makes the
`upToDate` check meaningful rather than decorative.

### The `upToDate` check, made durable
| Theorem | Statement |
|---|---|
| `Proof.voteDom_reachable` | Every vote-log record is backed by the grant that produced it |
| **`Proof.vote_dominates`** | **A vote means the elected leader's log dominates the voter's** — whoever wins term `U` was elected with a log at least as up to date as the log every one of its voters held when it voted |

`World.voteLogs` is the eighth ghost field, recording `(voter, term, log)` at the
instant a vote is granted. The `upToDate` check compares the candidate's
advertised log against the *voter's log at that instant*, so that log has to be
on record for the check to mean anything afterwards.

### The leader's log as a durable object, and what an ack means
| Theorem | Statement |
|---|---|
| `Proof.llInv_reachable` | **`World.leaderLogs` behaves as one growing object**: every snapshot is a prefix of the leader's current log while its term stands, snapshots for a `(node, term)` form a chain, and every minted entry lives in one |
| `Proof.leaderLog_both` | Two snapshots of one leader's term can be combined: whichever is longer holds both entries |
| `Proof.leaderLogWF_reachable` | Leader-log snapshots are well-formed logs |
| `Proof.msgFromLeaderLog_reachable` | **Every replication payload is a tail of a recorded log of its sender** — turning "the sender's log at some past moment" into a concrete record |
| `Proof.handleAppendEntries_ack`, `step_ack_shape` | A positive acknowledgement pins down the message that caused it, the index it covers, and how the log was reshaped |
| `Proof.roleTermPos_reachable`, `createdTermPos_reachable`, `wf_term_pos` | Campaigners and leaders have positive terms, hence so does every minted entry |
| **`Proof.ackAgrees_reachable`** | **A positive acknowledgement means the follower's log agrees with the leader's up to the acknowledged index.** This is the content the commit rule relies on: a leader counting `matchIndex` values is really counting replicas whose logs match its own |

### Commit records and their evidence
| Theorem | Statement |
|---|---|
| `Proof.WellFormedLog.mono` | Well-formedness survives a step, since `created` and `chain` only grow |
| `Proof.snapWF_reachable` | **Every log snapshotted into `commits`, `acks` or `elected` is a well-formed log**, so `wf_matching` applies to all of them |
| `Proof.ackRecorded_reachable` | Every successful acknowledgement on the wire has a snapshot record of the log that was acknowledged |
| `Proof.pm_get_set_self`, `pm_get_set_ne`, `pm_get_setAll` | Lookup laws for the peer-progress map |
| `Proof.step_matchIndex` | **How `matchIndex` can change**: untouched, one peer set from an ack in the leader's own term, or reset to zero on assuming leadership |
| **`Proof.miSound_reachable`** | **A leader's non-zero `matchIndex` is never invented** — it is always backed by a real acknowledgement from that peer in the leader's own term |
| **`Proof.matchIndex_ack`** | Whatever a leader believes a peer holds, that peer really did acknowledge, **and the log it acknowledged is on permanent record** |
| `Proof.replicatedOn_ok` | The quorum a leader counts is duplicate-free and made of real members |
| **`Proof.step_commit_quorum`** | **Advancing the commit index under leadership means a majority really did have the entry** — the only two sites that advance a leader's index route through `advanceCommit`; `handleAppendEntries` also moves it but demotes to follower first |
| `Proof.commitQuorum_reachable` | Every commit record's quorum is a genuine majority, and every member of it really did acknowledge that prefix in the leader's term — the leader included, via the standing self-acknowledgement `ackOf` records for a leader's own log |
| **`Proof.advanceCommit_spec`** | **What advancing the commit index guarantees**: the chosen index is strictly higher, carries an entry of the leader's *current* term (Raft's Figure-8 restriction), and is replicated on a majority per the leader's own `matchIndex` |

### Log Matching, generalised to snapshots
| Theorem | Statement |
|---|---|
| `Proof.WellFormedLog` | The two properties the Log Matching proof actually used: every entry was minted at its index, and every entry beyond the first carries its predecessor link |
| `Proof.wf_node` | Replicas' own logs are well formed |
| `Proof.wf_entry_unique`, `wf_agree_pred` | Entry uniqueness and the downward step, for arbitrary well-formed logs |
| **`Proof.wf_matching`** | **Log Matching for any two well-formed logs** — including ghost snapshots, which is what Leader Completeness reasons about |

Leader Completeness argues about the log a leader was *elected* with, the log it
*committed* against, and the log a follower *acknowledged* — none of which is a
live replica's current log. The original proof never used liveness, only the two
properties above, so generalising it was a matter of naming them.

`World.commits` and `World.acks` are the sixth and seventh ghost fields,
snapshotting `(leader, term, commitIndex, log)` and `(acker, term, matchIndex,
log)`. `acks` also carries a leader's standing acknowledgement of its own log,
which is what lets the quorum-intersection argument treat the committing leader
like any other replica.

### Groundwork for Leader Completeness
| Theorem | Statement |
|---|---|
| `Proof.eInv_reachable` | The election-record invariants hold in every reachable world |
| `Proof.ElectedPrefix` | **While a leader still holds the term it was elected for, the log it was elected with is a prefix of its current log** — leaders only append and cannot be demoted within their term |
| `Proof.elected_unique` | A term has at most one election record |
| `Proof.step_requestVote_log` | **A `requestVote` advertises exactly the sender's own `lastIndex`/`lastTerm`**, and campaigning does not disturb the log |
| `Proof.candidate_log_stable` | **A candidate's log does not move** — only `handleClientReq` and `appendFrom` touch a log, and the first demands leadership while the second demotes to follower |
| `Proof.candidate_term_grows` | Becoming a candidate strictly advances the term, so a node cannot re-enter candidacy in a term it has already campaigned in |
| `Proof.leader_from_candidate`, `leader_log_unchanged` | Assuming leadership without a term change means the node was campaigning, and does not move its log |
| `Proof.candInv_reachable` | `CandLog`: while a node is still campaigning in the term it advertised, the advertised `lastIndex`/`lastTerm` really are its own |
| **`Proof.rvElected_reachable`** | **`RVElected`: the log a leader was elected with is exactly the log it advertised** — this is what makes the voter's `upToDate` check a statement about the elected leader's real log |

`World.elected` is a fifth ghost field, capturing `(node, term, log)` at the
instant a node assumes leadership. Leader Completeness is a claim about the log a
leader held *when it won*, which no current-state predicate can express once that
leader has advanced. The log is stored as a `σ` value, so this needs no
lawfulness instance and leaves the executable path untouched.

### Groundwork for Log Matching, part two
| Theorem | Statement |
|---|---|
| `Proof.appendFrom_termAt` | **The term at each spliced index is the payload's term there** — true even in the branch that *keeps* an existing entry, since that branch fires only when the terms already agree |
| `Proof.appendFrom_get_above` | Beyond the spliced range the log is either untouched or has ended |
| `Proof.appendFrom_lastIndex_le` | A splice never leaves the log longer than the old log or the spliced range |
| `Proof.appendFrom_above_unchanged` | **Reaching beyond the spliced range means the splice changed nothing** — no conflict was found, so every step kept its existing entry |
| `Proof.get_isSome_below` | Logs have no holes |

`World.chain` is a fourth ghost field, recording for each minted entry the
**term of the entry directly beneath it**. Because a term at an index determines
the entry there (`log_entry_unique`), that recorded term determines the
predecessor entry, and chasing links downwards from a shared index is what will
force two logs to agree all the way to the start.

### Groundwork for Log Matching
| Theorem | Statement |
|---|---|
| `LogStore.lastIndex_truncFrom`, `lastIndex_truncFrom_of_le` | Truncation leaves exactly the prefix below the cut |
| `Proof.appendFrom_get_of_lt` | **Splicing an `AppendEntries` payload never disturbs the log below the splice point** — this is what makes `AppendEntries` idempotent under duplication and reordering |
| `Proof.appendFrom_lastIndex_ge` | A splice extends the log to cover everything it wrote |
| `Proof.appendFrom_one_lastIndex` | Writing one entry at `startIdx` leaves the log reaching exactly `startIdx` |
| `Proof.step_log_of_leader` | While a node remains leader, its log can only be extended by one entry — truncation lives only in `appendFrom`, reachable only via `handleAppendEntries`, which unconditionally demotes to follower |
| `Proof.step_appendEntries_leader` | `appendEntries` is only ever transmitted by a leader, stamped with its own term |
| `Proof.step_send_dest` | Every message goes either to a `Config.peers` member or back to whoever just wrote to us |
| `Proof.pInv_reachable` | In every reachable world: **no packet is self-addressed**, and **every `appendEntries` for term `t` was sent by the winner of term `t`** |
| **`Proof.leader_stable`** | **A leader keeps its role for as long as its term is unchanged** — leadership of a term is a single contiguous stretch, so a node cannot leave and re-enter leadership of the same term |
| **`Proof.leader_log_monotone`** | **A leader's log grows monotonically while it leads** — never truncated, never rewritten |

## All four safety properties are proved

Raft's four safety properties are all machine-checked, `sorry`-free, on the
three standard axioms:

| Property | Theorem | Statement |
|---|---|---|
| **Election Safety** | `Proof.electionSafety`, `Proof.everWinner_unique` | At most one node leads (indeed, *ever wins*) a given term |
| **Log Matching** | `Proof.logMatching` | Two logs holding an entry with the same index and term agree on every entry below it |
| **Leader Completeness** | `Proof.leaderCompleteness` | An entry committed in term `T` is present, at the same index, in the log of every leader elected in a later term |
| **State Machine Safety** | `Proof.stateMachineSafety` | Two replicas never apply different entries at the same log index |

```
lake env lean -- <<'X'
import RaftKV
#print axioms RaftKV.Proof.electionSafety
#print axioms RaftKV.Proof.logMatching
#print axioms RaftKV.Proof.leaderCompleteness
#print axioms RaftKV.Proof.stateMachineSafety
#print axioms RaftKV.Proof.replicas_agree
X
```

### Leader Completeness — how the circularity was broken

Every direct attempt needs *"a node that acknowledged a prefix still holds it
later"*, and every proof of that needs Leader Completeness. The way out is to
stop asking whether the node **kept** the prefix and ask instead **where its
current contents came from**:

| Theorem | Statement |
|---|---|
| **`Proof.changeAttributed_reachable`** | **Change attribution.** Wherever a node's log now stands, at every index it once acknowledged it agrees with *some recorded leader log* of a term between the acknowledgement's term and the node's own current term. Mentions no commit and no quorum, so it is provable outright; the term bound is what makes the eventual induction well-founded |
| **`Proof.ackHold_reachable`** | **While the acknowledged term still stands, the prefix is still held.** Within one term the leader is unique and its log only grows, so any payload arriving in that term either extends what the node already agreed with or matches it entry for entry — `appendFrom_id_of_match` then says the splice changed nothing |
| `Proof.voteAttributed_reachable` | The same statement about the log a voter held *when it voted*, with the witness term strictly below the vote's term |
| `Proof.electedAttributed_reachable` | ...and about the log a node was elected with, for the case where the intersecting node is the new leader itself |
| `Proof.voted_carry`, `Proof.handleRequestVote_grant_free` | A spent vote stays spent while the term stands, and a grant requires an unspent vote — this is what forces the attribution witness *below* the vote's term |
| **`Proof.dominate_carries`** | **Figure 9.** If a voter's log already agrees with the leader's up to a committed index, any log at least as up to date agrees too |
| `Proof.grantHasVoteLog_reachable`, `Proof.electedQuorum_reachable` | Every grant has a vote-log snapshot behind it, and every election record carries the quorum of grants that produced it |
| `Proof.commitQuorum_reachable` | Every commit record's quorum is a genuine majority, every member of which really did acknowledge that prefix in the leader's term |
| **`Proof.lc_aux`** | **The induction on the term itself.** The new leader's election quorum meets the commit's acknowledgement quorum at some node; attribution says where that node's log came from; the induction hypothesis carries the prefix from there onto it; domination carries it onto the new leader |
| **`Proof.leaderCompleteness`** | **Leader Completeness** |

Two protocol changes were needed to make the attribution argument go through,
both benign and both exercised by the running cluster:

* a node grants a vote only when `votedFor` is `none` (previously it would also
  re-grant to the same candidate); and
* accepting an `appendEntries` spends the term's vote on the sender if the node
  had not voted yet.

Together these make *"a node that has heard from a leader cannot vote again in
that term"*, which is exactly what bounds the attribution witness strictly below
the voting term and closes the induction.

A third change makes a follower's `commitIndex` monotone: it is now
`max` of the old index and the leader's claim, so a stale or short payload
cannot retract what a node already considers committed.

### State Machine Safety

| Theorem | Statement |
|---|---|
| **`Proof.committed_unique`** | **A committed index determines its entry** — the direct corollary of Leader Completeness |
| `Proof.appliedBound_reachable` | The state machine never runs past `commitIndex` |
| `Proof.sInv_reachable` (`CommitBound`, `MsgCommitted`, `AppliedCommitted`) | `commitIndex` is inside the log; what a leader advertises as committed really is; and everything a replica believes committed really is. These three are mutually dependent — a follower learns of commitment from a message, a leader's message is justified by its own belief — so they are carried as one invariant |
| **`Proof.splice_preserves`** | **A splice never disturbs anything the node already considers committed.** Every payload index at or below the commit index carries an entry the node already holds; by `AppliedCommitted` that entry is committed, and by Leader Completeness the sending leader holds it too, so the consistency scan finds no conflict there |
| **`Proof.stateMachineSafety`** | **State Machine Safety** |

### End to end: the refinement chain, closed

| Theorem | Statement |
|---|---|
| `KVStore.applyCmd_refines` | The executable state machine matches `Spec.applyCmd` — once, for every lawful implementation |
| `Proof.applyLoop_refines` | Draining the commit queue matches `Spec.applyAll` |
| **`Proof.smRefines_reachable`** | **In every reachable world, each replica's key/value state is exactly what the sequential specification produces from the commands that replica has applied** |
| **`Proof.replicas_agree`** | **Two replicas that have applied the same number of entries hold identical abstract state and answer every lookup identically** |

`replicas_agree` is the statement a client cares about, and it rests on all four
safety properties plus the storage abstractions' laws. Swapping `ArrayLog` or
`HashKV` for a faster implementation costs only a proof of that interface's
laws; every theorem above transports unchanged.

## Not proved

- **Liveness** — deliberately out of scope; Raft guarantees none without timing
  assumptions.
- **Linearizability** of the HTTP interface as a whole. `replicas_agree` gives
  replica agreement and specification conformance of the applied prefix, which
  is the state half of linearizability; the ordering half (that every client
  response corresponds to a point between invocation and return) is not
  formalised, and would need the request/response history in the model.
- **Crash recovery** — see "Known unsoundness" below.

## The proved properties, also tested

Because `step` is pure, randomised schedules with message loss, reordering,
duplication and concurrent elections are reproducible from a seed
(`RaftKV/Runtime/Random.lean`, driven by `Test/Random.lean`). Four properties
are checked after every run — one leader per term, entries determined by index
and term, prefixes agreeing below a shared entry, and applied entries never
disagreeing.

Result: **0 failures** across 710 schedules — 300 × 400 steps on 3 nodes,
200 × 800 on 5 nodes, 60 × 1200 on 3 nodes, and 150 × 600 on 4 nodes. The sweep
is not vacuous: 87/100 3-node runs end with an elected leader, and a
deliberately false check is caught 299 times out of 300.

This is now belt-and-braces rather than the primary evidence, and is not part of
the trusted path.

## Trusted base

Not verified, and relied upon:

1. The Lean kernel and compiler.
2. libuv, `Std.Http`'s HTTP/1.1 parser, and the OS.
3. `RaftKV.Frame` — the `List Token ↔ String` framing. The *semantic* half of the
   codec is proved; framing is tested only, because proving it needs
   `String.splitOn` lemmas Lean core does not provide. `Frame.selfCheck`
   re-decodes every outgoing message so a framing fault fails loudly at the
   sender instead of corrupting a peer.
4. `RaftKV.Runtime.Server` — the I/O shim. It makes no protocol decisions; it
   converts sockets and timers into `Event`s and executes `Action`s.

## Known unsoundness in the running system

**There is no durable storage.** `currentTerm`, `votedFor` and the log live in
memory only. Real Raft requires these to be persisted before responding, because
a node that restarts and forgets its vote can vote twice in one term — exactly
what `vote_uniqueness` forbids in the model. The model does not include crashes,
so it does not detect this; the gap is real and is what the `Durability` seam
exists to close. Until then, treat a restarted replica as a new node, and do not
run this as a real datastore.
