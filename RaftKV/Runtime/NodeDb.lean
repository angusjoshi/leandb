import RaftKV.Runtime.PageFile
import RaftKV.Storage.NodeTree
import RaftKV.Storage.NodePersist
import RaftKV.Storage.KVHash

/-!
# A node's durable state, in the copy-on-write B-tree

The two-region store rewrites a node's *entire* durable image on every durable
change — the whole log and the whole state-machine snapshot, for one appended
entry. That is O(everything) per operation, and it is the last thing in this
repository that is wrong by a factor that grows with the data rather than by a
constant.

Here the durable state is spread over keys in one B-tree, so a commit writes only
the pages on the paths to the keys that actually changed: one root-to-leaf path
per changed key, and nothing else. Appending an entry is O(log n) instead of
O(log size + state size).

## Key layout

One tree holds everything, with the key space interleaved so nothing collides:

| key | holds |
|---|---|
| `0` | the scalars: term, vote, the log's window, the snapshot index |
| `2 * i`, `i ≥ 1` | the log entry at index `i` |
| `2 * j + 1` | the `j`-th binding of the state-machine snapshot |

Index `0` never holds a log entry, so key `0` is free for the header.

## What this does not fix

A compaction still rewrites the whole snapshot, because the snapshot is a list of
bindings with no stable order — `KVStore.toPairs` of a hash map may permute
between calls, so there is nothing to diff against. That is O(state) once per
`compactEvery` applied entries, so O(state / 1024) amortised per operation rather
than O(state) per operation, which is the improvement this file is for; it is not
zero.

Making it zero means the state machine itself living in this tree, with a
compaction retaining the old root rather than copying anything — free, because
the tree is already copy-on-write and already never reclaims. That needs the tree
to take `String` keys, which is a change to `RaftKV.Storage.BTree` and its
proofs, and is deliberately not attempted here.

**Not verified, and in the trusted base**, on the same footing as
`RaftKV.Runtime.Store`: this file, the layout above, and everything
`RaftKV.Runtime.PageFile` already carries.
-/

namespace RaftKV.NodeDb

open RaftKV Protocol RaftKV.PageFile RaftKV.NodeTree

/--
The operations that turn `before` into `after`.

Only what actually differs: appending one entry is one write and a header
update, and nothing else is touched.

**This is the shim's obligation**, on the same footing as `RaftKV.Runtime.Store`
performing exactly `Format.commitOps`: that applying this batch to the view of
`before` yields the view of `after`. `RaftKV.NodeTree.crash_recovers_node` takes
that as its hypothesis and concludes the crash safety; `Test/NodeDb.lean`
exercises it against appends, truncations, compactions and reopens.
-/
def delta (before after : Persistent ArrayLog) : List Op :=
  let m0 := metaOf before
  let m1 := metaOf after
  let header : List Op :=
    if m0 == m1 then [] else [(metaKey, some (encMeta m1).toByteArray)]
  -- entries that left the window, at the front by compaction or at the back by
  -- a truncating splice
  let gone : List Op :=
    ((List.range (m1.base - m0.base)).map (fun d => (logKey (m0.base + 1 + d), none)))
      ++ (if m1.size < m0.size then
            (List.range (m0.size - m1.size)).map (fun d => (logKey (m1.size + 1 + d), none))
          else [])
  -- entries that are new or have been overwritten
  let lo := max m0.base m1.base
  let live : List Op :=
    (List.range (m1.size - lo)).filterMap (fun d =>
      let i := lo + 1 + d
      let e := entryAt after.log i
      if entryAt before.log i == e then none
      else e.map (fun e => (logKey i, some (ByteCodec.enc e).toByteArray)))
  -- the snapshot, rewritten only when it changes
  let snap : List Op :=
    if before.snapPairs == after.snapPairs then []
    else
      (after.snapPairs.zipIdx.map (fun (kv, j) =>
          (snapKey j, some (ByteCodec.enc kv.1 ++ ByteCodec.enc kv.2 : List UInt8).toByteArray)))
        ++ (if after.snapPairs.length < before.snapPairs.length then
              (List.range (before.snapPairs.length - after.snapPairs.length)).map
                (fun d => (snapKey (after.snapPairs.length + d), none))
            else [])
  header ++ gone ++ live ++ snap

/-- Publish a durable change: one commit, whatever it touched. -/
def save (db : Db) (before after : Persistent ArrayLog) : IO Unit :=
  db.update (delta before after)

/-- Write a node's durable state from scratch, for a fresh database. -/
def saveAll (db : Db) (p : Persistent ArrayLog) : IO Unit :=
  save db { currentTerm := 0, votedFor := none, log := LogStore.empty,
            snapIndex := 0, snapPairs := [] } p

/-- Read a node's durable state back, or `none` if there is not one yet. -/
def load (db : Db) : IO (Option (Persistent ArrayLog)) := do
  match ← db.get metaKey with
  | none => return none
  | some raw =>
      match decMeta raw.toList with
      | none => return none
      | some m =>
          let mut es : Array Entry := #[]
          for d in List.range (m.size - m.base) do
            let i := m.base + 1 + d
            match ← db.get (logKey i) with
            | none => throw (IO.userError s!"log entry {i} missing from the page file")
            | some bs =>
                match (ByteCodec.dec bs.toList : Option (Entry × List UInt8)) with
                | none => throw (IO.userError s!"log entry {i} does not decode")
                | some (e, _) => es := es.push e
          let mut ps : List (String × String) := []
          for j in List.range m.snapCount do
            match ← db.get (snapKey j) with
            | none => throw (IO.userError s!"snapshot binding {j} missing from the page file")
            | some bs =>
                match (ByteCodec.dec bs.toList : Option (String × List UInt8)) with
                | none => throw (IO.userError s!"snapshot binding {j} does not decode")
                | some (k, r) =>
                    match (ByteCodec.dec r : Option (String × List UInt8)) with
                    | none => throw (IO.userError s!"snapshot binding {j} has no value")
                    | some (v, _) => ps := ps ++ [(k, v)]
          return some { currentTerm := m.currentTerm, votedFor := m.votedFor,
                        log := ⟨m.base, es⟩, snapIndex := m.snapIndex, snapPairs := ps }

/-- Restore a node from the page file, or start it fresh. -/
def loadNode (db : Db) (cfg : Config) : IO (NodeState ArrayLog HashKV) := do
  match ← load db with
  | none => return Protocol.initState cfg
  | some st => return Protocol.recoverNode cfg st

end RaftKV.NodeDb
