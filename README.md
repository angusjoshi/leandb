# raftkv — a Raft-replicated key/value store in Lean 4

Multiple replicas, aware of each other, each exposing an HTTP key/value API
backed by a Raft-replicated log. The protocol core is a pure function, and
**all four of Raft's safety properties are machine-checked in Lean**:

| Property | Theorem |
|---|---|
| Election Safety | `Proof.electionSafety` |
| Log Matching | `Proof.logMatching` |
| Leader Completeness | `Proof.leaderCompleteness` |
| State Machine Safety | `Proof.stateMachineSafety` |

On top of those, the refinement chain down to what a client observes is closed:

```lean
theorem replicas_agree (hnd : members.Nodup) (hrch : Reachable members w)
    (heq : (w.nodes i).lastApplied = (w.nodes j).lastApplied) :
    LawfulKVStore.toModel (w.nodes i).kv = LawfulKVStore.toModel (w.nodes j).kv
      ∧ ∀ k, KVStore.find (w.nodes i).kv k = KVStore.find (w.nodes j).kv k
```

together with `Proof.smRefines_reachable`: every replica's key/value state is
exactly what the sequential specification `Spec.run` produces from the commands
that replica has applied. Everything is `sorry`-free on Lean's three standard
axioms. See **[PROOFS.md](PROOFS.md)** for the full inventory, the trusted base,
and what is deliberately *not* proved (liveness, the ordering half of
linearizability, crash recovery).

## Run a 3-node cluster

```bash
lake build
for i in 0 1 2; do ./.lake/build/bin/raftkv $i 3 9000 & done
# raft ports 9000+id, http ports 9100+id

curl -s localhost:9100/status
curl -s -X PUT --data-binary 'hello raft' localhost:9100/kv/greeting
curl -s localhost:9100/kv/greeting          # -> hello raft
curl -s -X DELETE localhost:9100/kv/greeting
curl -s localhost:9101/kv/greeting          # -> 503, "not leader; try node 0"
```

Kill the leader and the cluster elects a new one, retaining committed data.

## Design

The Raft node is a **pure function**

```lean
step : NodeState σ κ → Event → NodeState σ κ × List Action
```

with no `IO` anywhere. The runtime turns sockets and timers into `Event`s and
executes the `Action`s. Asynchrony, reordering, loss and duplication exist only
in the proof-level `World` relation, never in the code. That is what makes the
safety proofs proofs about a pure function rather than about a concurrent
program.

### Abstractions with composable proofs

Every component with a simple-now/fast-later split sits behind a two-class
interface: operations (executable) and laws (a `toModel` refinement mapping plus
equations). Protocol proofs quantify over the interface and mention only the
model, so **swapping an implementation costs exactly a proof of that
interface's laws** — every downstream theorem transports unchanged.

| Seam | Interface | Model | Now | Later |
|---|---|---|---|---|
| Log | `LogStore` / `LawfulLogStore` | `List Entry` | `ArrayLog` | segmented mmap'd log |
| State machine | `KVStore` / `LawfulKVStore` | `Spec.KVModel` | `HashKV` | persistent/CoW map |
| Wire format | `Codec` | round-trip law | token encoding | compact binary |
| Transport | `World.sent` | adversarial network | conn-per-message TCP | pooled/pipelined |

The split into two classes matters: a memory-mapped log cannot *compute* its
full contents as a `List Entry`, so `toModel` lives in the lawful class, which
may be `noncomputable` without affecting the executable path. Note also there is
no `toList` **operation** — materialising the log is a proof-level fiction.

## Layout

```
RaftKV/
  Core/Types.lean        commands, replies, log entries
  Spec/KV.lean           the sequential specification (top of the refinement chain)
  Storage/               LogStore + ArrayLog, KVStore + HashKV
  Protocol/
    Types.lean           messages, events, actions, node state
    Node.lean            step — the whole protocol, pure
    Codec.lean           token encoding, round-trip proved
    Frame.lean           framing (trusted, tested)
    Network.lean         World / Step / Reachable + safety statements
  Proof/                 29 modules, ~9.7k lines:
                         quorum intersection, terms, votes, election safety,
                         log matching, change attribution, leader completeness,
                         state machine safety, state-machine refinement
  Runtime/
    Sim.lean             deterministic in-process cluster simulator
    Server.lean          the I/O shim (trusted)
```

`Test/Sim.lean` runs a 3-node cluster in-process with no sockets — because
`step` is pure, any schedule replays exactly.
