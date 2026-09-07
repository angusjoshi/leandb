import RaftKV.Storage.BTreeContents
import RaftKV.Storage.Bytes
import RaftKV.Protocol.Network

/-!
# A node's durable state as B-tree contents

The two-region store of `RaftKV.Storage.Persist` rewrites a node's *entire*
durable image on every durable change — the whole log and the whole
state-machine snapshot, for one appended entry. This file says what it means to
hold that state as **keys in a copy-on-write B-tree** instead, so that a commit
writes only the root-to-leaf paths of the keys that actually changed.

`RaftKV.BTree.batch_commit` is the storage-level theorem: one commit, however
many keys it touched, publishes all of them or none, and until the root cell
moves the old tree is byte-for-byte what it was. What is left is to say which
keys a node's durable state occupies and that they determine it, which is what
`viewOf` and `viewOf_injective` do — and then `crash_recovers_node` below is the
same statement `RaftKV.Disk.crash_recovers_node` makes for the two-region store:
a crash during a commit leaves a tree that reads back as one of the two node
states the model's `crash` rule permits, and nothing else.

## Key layout

One tree holds everything, with the key space interleaved so nothing collides:

| key | holds |
|---|---|
| `0` | the scalars: term, vote, the log's window, the snapshot index |
| `2 * i`, `i ≥ 1` | the log entry at index `i` |
| `2 * j + 1` | the `j`-th binding of the state-machine snapshot |

Index `0` never holds a log entry, so key `0` is free for the header.

## What is proved here, and what is trusted

Proved: the layout determines the state (`viewOf_injective`), and a commit of a
batch that realises a change is crash-safe (`crash_recovers_node`).

Trusted, on the same footing as `RaftKV.Runtime.Store` performing exactly
`Format.commitOps`: that `RaftKV.NodeDb.delta` computes a batch which realises
the change — that is, that applying it to the view of the old state yields the
view of the new one. `Test/NodeDb.lean` exercises it against appends,
truncations, compactions and reopens.
-/

namespace RaftKV.NodeTree

open RaftKV Protocol RaftKV.BTree

/-- The key holding the header. -/
def metaKey : Nat := 0

/-- The key holding the log entry at index `i`. -/
def logKey (i : Nat) : Nat := 2 * i

/-- The key holding the `j`-th snapshot binding. -/
def snapKey (j : Nat) : Nat := 2 * j + 1

/-- The scalars, and enough shape to read the rest back. -/
structure Meta where
  /-- Latest term the node has seen. -/
  currentTerm : Nat
  /-- Who it voted for in that term, if anyone. -/
  votedFor : Option Nat
  /-- Entries at or below this have been discarded. -/
  base : Nat
  /-- Highest index the log reaches. -/
  size : Nat
  /-- The index the snapshot covers. -/
  snapIndex : Nat
  /-- How many bindings the snapshot has. -/
  snapCount : Nat
  deriving Repr, DecidableEq, Inhabited

/--
The header's bytes.

A `List UInt8` rather than a `ByteArray`: the round trip that matters is
`ByteCodec`'s, and `List.toByteArray` has no round-trip lemma in core. The shim
stores `(encMeta m).toByteArray` and reads `.toList` back, which is the same
correspondence `RaftKV.Runtime.Store` already relies on.
-/
def encMeta (m : Meta) : List UInt8 :=
  ByteCodec.enc m.currentTerm ++ ByteCodec.enc m.votedFor.isSome
    ++ ByteCodec.enc (m.votedFor.getD 0) ++ ByteCodec.enc m.base ++ ByteCodec.enc m.size
    ++ ByteCodec.enc m.snapIndex ++ ByteCodec.enc m.snapCount

def decMeta (bs : List UInt8) : Option Meta := do
  let (t, r) ← (ByteCodec.dec bs : Option (Nat × List UInt8))
  let (hasVote, r) ← (ByteCodec.dec r : Option (Bool × List UInt8))
  let (vote, r) ← (ByteCodec.dec r : Option (Nat × List UInt8))
  let (base, r) ← (ByteCodec.dec r : Option (Nat × List UInt8))
  let (size, r) ← (ByteCodec.dec r : Option (Nat × List UInt8))
  let (snapIndex, r) ← (ByteCodec.dec r : Option (Nat × List UInt8))
  let (snapCount, _) ← (ByteCodec.dec r : Option (Nat × List UInt8))
  some { currentTerm := t, votedFor := if hasVote then some vote else none,
         base, size, snapIndex, snapCount }

/-- The header a durable state implies. -/
def metaOf (p : Persistent ArrayLog) : Meta :=
  { currentTerm := p.currentTerm, votedFor := p.votedFor,
    base := p.log.base, size := p.log.base + p.log.entries.size,
    snapIndex := p.snapIndex, snapCount := p.snapPairs.length }

/-- The entry a durable log holds at index `i`, if it still holds one. -/
def entryAt (lg : ArrayLog) (i : Nat) : Option Entry :=
  if i ≤ lg.base then none else lg.entries[i - lg.base - 1]?

/-- The header round-trips. -/
theorem decMeta_encMeta (m : Meta) : decMeta (encMeta m) = some m := by
  obtain ⟨t, vf, base, size, si, sc⟩ := m
  have hass : ∀ (a b c d e f g : List UInt8),
      a ++ b ++ c ++ d ++ e ++ f ++ g = a ++ (b ++ (c ++ (d ++ (e ++ (f ++ g))))) := by
    intro a b c d e f g; simp [List.append_assoc]
  unfold encMeta decMeta
  cases vf with
  | none =>
      simp only [Option.isSome, Option.getD, hass]
      rw [ByteCodec.dec_enc]
      simp only [bind, Option.bind]
      rw [ByteCodec.dec_enc]; simp only
      rw [ByteCodec.dec_enc]; simp only
      rw [ByteCodec.dec_enc]; simp only
      rw [ByteCodec.dec_enc]; simp only
      rw [ByteCodec.dec_enc]; simp only
      rw [ByteCodec.dec_enc_nil]
      simp
  | some c =>
      simp only [Option.isSome, Option.getD, hass]
      rw [ByteCodec.dec_enc]
      simp only [bind, Option.bind]
      rw [ByteCodec.dec_enc]; simp only
      rw [ByteCodec.dec_enc]; simp only
      rw [ByteCodec.dec_enc]; simp only
      rw [ByteCodec.dec_enc]; simp only
      rw [ByteCodec.dec_enc]; simp only
      rw [ByteCodec.dec_enc_nil]
      simp

/-- The bytes a durable state puts at each key. -/
def viewOf (p : Persistent ArrayLog) : Nat → Option (List UInt8) := fun k =>
  if k = 0 then some (encMeta (metaOf p))
  else if k % 2 = 0 then (entryAt p.log (k / 2)).map ByteCodec.enc
  else (p.snapPairs[(k - 1) / 2]?).map (fun kv => ByteCodec.enc kv.1 ++ ByteCodec.enc kv.2)

/-! ## The layout determines the state -/

/-- Two states with the same header agree on every scalar. -/
theorem metaOf_inj {p q : Persistent ArrayLog} (h : encMeta (metaOf p) = encMeta (metaOf q)) :
    metaOf p = metaOf q := by
  have := decMeta_encMeta (metaOf p)
  rw [h, decMeta_encMeta (metaOf q)] at this
  exact (Option.some.inj this).symm

/--
**The layout determines the durable state.**

Two node states that put the same bytes at every key are the same state — so a
tree that reads back as `viewOf p` can only have come from `p`, and recovery
cannot produce anything else.
-/
theorem viewOf_injective {p q : Persistent ArrayLog} (h : viewOf p = viewOf q) : p = q := by
  -- the header pins every scalar, including the log's window and the two counts
  have hm : metaOf p = metaOf q := by
    refine metaOf_inj ?_
    have := congrFun h 0
    unfold viewOf at this
    rw [if_pos rfl, if_pos rfl] at this
    exact Option.some.inj this
  have hbase : p.log.base = q.log.base := congrArg Meta.base hm
  have hsize : p.log.base + p.log.entries.size = q.log.base + q.log.entries.size :=
    congrArg Meta.size hm
  have hcount : p.snapPairs.length = q.snapPairs.length := congrArg Meta.snapCount hm
  -- the entries, index by index
  have hent : p.log.entries = q.log.entries := by
    have hlen : p.log.entries.size = q.log.entries.size := by omega
    refine Array.ext hlen ?_
    intro i hi hi'
    have := congrFun h (2 * (p.log.base + i + 1))
    unfold viewOf at this
    rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)] at this
    have hdiv : 2 * (p.log.base + i + 1) / 2 = p.log.base + i + 1 := by omega
    rw [hdiv] at this
    unfold entryAt at this
    rw [if_neg (by omega), if_neg (by omega)] at this
    have e1 : p.log.base + i + 1 - p.log.base - 1 = i := by omega
    have e2 : p.log.base + i + 1 - q.log.base - 1 = i := by omega
    rw [e1, e2] at this
    rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hi'] at this
    simp only [Option.map_some] at this
    have := Option.some.inj this
    exact ByteCodec.enc_injective this
  -- and the snapshot bindings, position by position
  have hsnap : p.snapPairs = q.snapPairs := by
    refine List.ext_getElem hcount ?_
    intro j hj hj'
    have := congrFun h (2 * j + 1)
    unfold viewOf at this
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)] at this
    have hdiv : (2 * j + 1 - 1) / 2 = j := by omega
    rw [hdiv] at this
    rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj'] at this
    simp only [Option.map_some] at this
    have hb := Option.some.inj this
    have h1 := ByteCodec.dec_enc (p.snapPairs[j].1) (ByteCodec.enc p.snapPairs[j].2)
    rw [hb] at h1
    rw [ByteCodec.dec_enc] at h1
    have hk : q.snapPairs[j].1 = p.snapPairs[j].1 := (Prod.mk.inj (Option.some.inj h1)).1
    have hv : ByteCodec.enc q.snapPairs[j].2 = ByteCodec.enc p.snapPairs[j].2 :=
      (Prod.mk.inj (Option.some.inj h1)).2
    have := ByteCodec.enc_injective hv
    exact Prod.ext hk.symm this.symm
  obtain ⟨t1, v1, ⟨b1, e1⟩, s1, ps1⟩ := p
  obtain ⟨t2, v2, ⟨b2, e2⟩, s2, ps2⟩ := q
  simp only at hbase hent hsnap
  have ht : t1 = t2 := congrArg Meta.currentTerm hm
  have hv : v1 = v2 := congrArg Meta.votedFor hm
  have hs : s1 = s2 := congrArg Meta.snapIndex hm
  subst ht; subst hv; subst hs; subst hbase; subst hent; subst hsnap
  rfl

/-! ## Crash safety, end to end

The same statement `RaftKV.Disk.crash_recovers_node` makes for the two-region
store: a crash at any point of a commit leaves the store holding a node state the
model's `crash` rule permits, and nothing else.
-/

/-- A tree reads back as a node's durable state. -/
def Holds (t : Tree) (pages : Pages) (p : Persistent ArrayLog) : Prop :=
  ∀ k, (t.lookup pages k).map ByteArray.toList = viewOf p k

/--
**A crash during a commit rebuilds a node the model allows.**

Let the tree hold node `s`'s durable projection, and let `ops` be a batch that
realises the change to `s'` — the shim's obligation, exactly as
`RaftKV.Runtime.Store` is obliged to perform `Format.commitOps`. Then:

* the new root cell reads back `s'`; and
* **whatever the crash did** — any image agreeing with the pre-commit one below
  the old mark, so arbitrary garbage in the whole range the batch was
  allocating, and any subset of its writes having landed, in any order — the old
  root cell still reads back `s`.

So recovery yields `Protocol.restart s` or `Protocol.restart s'`, and by
`viewOf_injective` nothing else is possible.
-/
theorem crash_recovers_node {t t' : Tree} {pages : Pages} {m : List (Nat × ByteArray)}
    {ops : List Op} {ws : List (Nat × Node)} {d : Nat}
    (s s' : Persistent ArrayLog)
    (hwf : WFd t pages d m) (hd : d + ops.length < maxDepth)
    (hbatch : t.batch pages ops = some (t', ws))
    (hbefore : ∀ k, (lookupList m k).map ByteArray.toList = viewOf s k)
    (hafter : ∀ k, (lookupList (applyOps m ops) k).map ByteArray.toList = viewOf s' k) :
    Holds t' (patch pages ws) s'
      ∧ ∀ (g : Pages), (∀ q, q < t.next → g q = pages q) →
          ∀ (ws' : List (Nat × Node)), (∀ w ∈ ws', w ∈ ws) → Holds t (patch g ws') s := by
  obtain ⟨hnew, _, hold⟩ := batch_commit hwf hd hbatch
  refine ⟨fun k => by rw [hnew k]; exact hafter k, fun g hg ws' hsub k => ?_⟩
  rw [(hold g hg ws' hsub).1 k]
  exact hbefore k

/-- And the state it reads back is the only one it could be. -/
theorem holds_unique {t : Tree} {pages : Pages} {p q : Persistent ArrayLog}
    (hp : Holds t pages p) (hq : Holds t pages q) : p = q :=
  viewOf_injective (funext fun k => (hp k).symm.trans (hq k))

end RaftKV.NodeTree
