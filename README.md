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

…and they hold in a model that includes **node crashes**: `Step` has a `crash`
rule under which the durable trio (`currentTerm`, `votedFor`, the log) survives
and everything else is rebuilt.

On top of those, **the store is proved linearizable** — one theorem, saying the
whole thing:

```lean
theorem linearizable (hnd : members.Nodup) (hrch : Reachable members w)
    (hfresh : Protocol.FreshIds w) :
    ∃ L : List Entry,
      -- 1. every answer is the sequential specification's answer, at its place in `L`
      (∀ t rid n r, Protocol.Answered w t rid n r →
          ∃ e, L[n - 1]? = some e ∧ e.reqId = rid
            ∧ r = (Spec.applyCmd (Spec.run ((L.take (n - 1)).map Entry.cmd)) e.cmd).2)
      -- 2. `L` never contradicts real time
      ∧ (∀ tA ridA nA rA tB ridB tB' nB rB,
          Protocol.Answered w tA ridA nA rA →
          Protocol.Submitted w tB ridB →
          Protocol.Answered w tB' ridB nB rB →
          tA < tB → nA < nB)
      -- 3. every replica has executed a prefix of `L`
      ∧ (∀ i, LawfulKVStore.toModel (w.nodes i).kv
            = Spec.run ((L.take (w.nodes i).lastApplied).map Entry.cmd))
```

In words: **there is one order `L` on the committed commands such that every
answer the cluster ever gave is the answer a single, sequential key/value store
would have given at that point in `L`; that order never contradicts real time;
and every replica has executed a prefix of it.** The only assumption beyond
reachability is that clients use distinct request ids.

### Storage, on a device that tears writes

The implementation that justifies the crash rule is proved too, on a device
model with **three** levels of durability rather than two:

| Where a byte is | What a crash does | How it got there |
|---|---|---|
| this process's buffer | lost outright | a plain write |
| the operating system | *may or may not* have landed, per address | `flush` |
| the platter | survives | `fsync` |

That distinction is the point. A two-level model cannot tell flushing from
fsyncing, and a proof written against one is satisfied by an implementation that
only ever flushes — which is broken. So there are two theorems:

* **`Disk.Format.commit_crash_safe`** — crash at **any** of the six points of a
  commit (`writeAt · flushUser · fsync · setRoot · flushUser · fsync`) and the
  store holds either the old value or the new one. Never a mixture.
* **`Disk.flushOnly_not_crash_safe`** — a commit that flushes but never fsyncs
  is **not** crash-safe: here is a device, a commit, and a crash after which
  recovery returns *neither* value, because the root swap reached the platter
  and the image did not.

`Disk.crash_recovers_node` bridges to the model: what the device gives back
always rebuilds to one of the two node states `World.crash` permits.

Lean's `IO.FS` has no `fsync` — its `flush` is `fflush` — so `RaftKV.Posix` is a
small FFI binding to `open`, `pread`, `pwrite`, `fsync` and `close`, and the
store is built on that. It is what makes the implementation match the proof
rather than approximate it.

The encoding round-trips all the way down (`ByteCodec`), including strings —
via code points rather than UTF-8, since Lean's core proves no round-trip for
`String.fromUTF8?` and using it would have added a trusted law.

Everything is `sorry`-free on Lean's three standard axioms. See
**[PROOFS.md](PROOFS.md)** for the full inventory, the trusted base, and what is
deliberately *not* proved (liveness, exactly-once client retries).

## Run a 3-node cluster

```bash
lake build
for i in 0 1 2; do ./.lake/build/bin/raftkv $i 3 9000 ./data & done
# raft ports 9000+id, http ports 9100+id
# the last argument is a data directory; omit it to run without persistence

curl -s localhost:9100/status
curl -s -X PUT --data-binary 'hello raft' localhost:9100/kv/greeting
curl -s localhost:9100/kv/greeting          # -> hello raft
curl -s -X DELETE localhost:9100/kv/greeting
curl -s localhost:9101/kv/greeting          # -> 503, "not leader; try node 0"
```

Kill the leader and the cluster elects a new one, retaining committed data. Kill
*every* node and restart them: with a data directory they recover their term,
their vote and their log from disk, and committed keys read back.

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
  Proof/                 30 modules, ~10.6k lines:
                         quorum intersection, terms, votes, election safety,
                         log matching, change attribution, leader completeness,
                         state machine safety, state-machine refinement,
                         linearizability
  Storage/
    Disk.lean            the device: torn writes, three durability levels, one atomic cell
    Persist.lean         copy-on-write commit, proved crash-safe
    Bytes.lean           ByteCodec, round-trip proved down to String
    NodePersist.lean     the bridge from the store to the model's crash rule
  Runtime/
    Sim.lean             deterministic in-process cluster simulator
    Posix.lean           FFI: open/pread/pwrite/fsync/close (trusted)
    Store.lean           the durable store on a real filesystem (trusted)
    Server.lean          the I/O shim (trusted)
c/raftkv_io.c            the C shim behind Posix.lean
```

`Test/Sim.lean` runs a 3-node cluster in-process with no sockets — because
`step` is pure, any schedule replays exactly.
