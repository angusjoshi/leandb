import RaftKV.Storage.Bytes
import RaftKV.Storage.Crc32

/-!
# A copy-on-write B-tree

The store the two-region superblock cannot be: it commits by writing only the
pages it changed, so an append costs a path rather than the whole image, and it
is where log compaction wants to live.

## The discipline

Exactly the one `RaftKV.Storage.Persist` proves crash-safe, at page granularity:

* **nothing reachable from the live root is ever overwritten.** An update copies
  every node on the root-to-leaf path into *fresh* pages and leaves the originals
  alone, so a reader following the old root sees a tree that has not moved.
* pages are allocated by bumping a high-water mark, never reused within a
  commit, which is what makes the previous point true by arithmetic rather than
  by an invariant about free lists.
* the commit point is the root cell: one atomic write naming the new root page
  and the new high-water mark.

## Checksums

Every page carries a CRC-32 over its own bytes and a page number. A page that
was torn by a crash, or that the drive quietly returned wrong, fails the check
and reads as `none` rather than as a plausible node with a garbage child
pointer. The page number is included so that a *stale but individually valid*
page — the classic misdirected-write failure — is caught too.

The checksum is deliberately **not** part of the crash-safety proof. That proof
rules out reading a torn page at all, by never overwriting what the live root
can reach; the checksum is defence in depth for the failures the model does not
claim to cover.

## What is proved and what is not

`fresh` and `frame` — the two laws that make a crash survivable — hold here by
construction, because allocation only ever hands out pages at or above the
high-water mark and the reader refuses to follow a pointer at or above it.
`correct` — that the tree actually stores what you put in it — is tested, not
proved; it is a statement about search, not about durability.

## Limits, stated

* Values must fit in a page. Overflow chains are not implemented.
* Deletion does not rebalance: nodes may become underfull. That wastes space and
  is otherwise harmless for a map.
* Pages left behind by a commit are not reclaimed. A free-list would need its
  own crash-safety argument, so it is deliberately absent for now.
-/

namespace RaftKV.BTree

open RaftKV

/-- Bytes per page. -/
def pageSize : Nat := 4096

/-- Bytes of page header: a CRC-32 and the page number it is meant to be. -/
def headerSize : Nat := 8

/-- A node: either leaf records or separators with children. -/
inductive Node where
  /-- Key/value records, sorted by key. -/
  | leaf (recs : Array (Nat × ByteArray))
  /-- `keys.size + 1` children; `keys[i]` separates `children[i]` from `children[i+1]`. -/
  | branch (keys : Array Nat) (children : Array Nat)
  deriving Inhabited

instance : ByteCodec Node where
  enc
    | .leaf recs => 0 :: ByteCodec.enc recs
    | .branch keys children => 1 :: (ByteCodec.enc keys ++ ByteCodec.enc children)
  dec bs :=
    match bs with
    | [] => none
    | t :: rest =>
        if t == 0 then
          match (ByteCodec.dec rest : Option (Array (Nat × ByteArray) × List UInt8)) with
          | none => none
          | some (recs, r) => some (.leaf recs, r)
        else if t == 1 then
          match (ByteCodec.dec rest : Option (Array Nat × List UInt8)) with
          | none => none
          | some (keys, r) =>
              match (ByteCodec.dec r : Option (Array Nat × List UInt8)) with
              | none => none
              | some (children, r') => some (.branch keys children, r')
        else none
  dec_enc := by
    intro n rest
    cases n with
    | leaf recs =>
        show (match (0 : UInt8) :: (ByteCodec.enc recs ++ rest) with
          | [] => none | t :: r => _) = _
        simp only [List.append_eq]
        rw [if_pos (by decide), ByteCodec.dec_enc recs rest]
    | branch keys children =>
        show (match (1 : UInt8) :: ((ByteCodec.enc keys ++ ByteCodec.enc children) ++ rest) with
          | [] => none | t :: r => _) = _
        simp only [List.append_eq, List.append_assoc]
        rw [if_neg (by decide), if_pos (by decide),
          ByteCodec.dec_enc keys (ByteCodec.enc children ++ rest)]
        dsimp only
        rw [ByteCodec.dec_enc children rest]

end RaftKV.BTree

namespace RaftKV.BTree

open RaftKV

/-! ## Pages

A page is a fixed-size byte image:

```
  0..3    CRC-32 of bytes 4..pageSize
  4..7    the page number this image belongs at, little-endian
  8..      the encoded node, zero-padded to the end
```

The page number lives *inside* the checksummed region on purpose. A drive that
returns the wrong sector, or a controller that wrote a page to the wrong place,
produces bytes whose own CRC is perfectly valid; only comparing the recorded
page number against the one we asked for catches that. Together the two fields
turn a torn write, a bit-rotted sector and a misdirected write into a clean
`none` rather than a node with a plausible-looking pointer in it.
-/

/-- Little-endian four bytes. -/
def putU32 (v : UInt32) : List UInt8 :=
  [v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8]

/-- Read little-endian four bytes at `off`, or zero if out of range. -/
def getU32 (bs : ByteArray) (off : Nat) : UInt32 :=
  let b (i : Nat) : UInt32 := if h : off + i < bs.size then (bs[off + i]'h).toUInt32 else 0
  b 0 ||| (b 1 <<< 8) ||| (b 2 <<< 16) ||| (b 3 <<< 24)

/-- Does this node's encoding fit in a page? -/
def fits (n : Node) : Bool := headerSize + (ByteCodec.enc n).length ≤ pageSize

/--
Serialise `n` as the image of page `pno`.

`none` when the node does not fit, which for a leaf means a single record larger
than a page — the overflow case this implementation does not handle.
-/
def encodePage (pno : Nat) (n : Node) : Option ByteArray :=
  let body := ByteCodec.enc n
  if headerSize + body.length ≤ pageSize then
    let payload := putU32 pno.toUInt32 ++ body
    let padded := payload ++ List.replicate (pageSize - 4 - payload.length) 0
    let withoutCrc : ByteArray := ⟨padded.toArray⟩
    let crc := Crc32.over withoutCrc
    some ⟨(putU32 crc ++ padded).toArray⟩
  else none

/--
Parse the image of page `pno`, rejecting anything that fails its checksum or
claims to be a different page.
-/
def decodePage (pno : Nat) (bs : ByteArray) : Option Node :=
  if bs.size ≠ pageSize then none
  else
    let stored := getU32 bs 0
    if Crc32.overRange bs 4 pageSize ≠ stored then none
    else if getU32 bs 4 ≠ pno.toUInt32 then none
    else match (ByteCodec.dec (bs.extract headerSize pageSize).toList : Option (Node × List UInt8)) with
      | some (n, _) => some n
      | none => none

/-! ## The tree -/

/--
The root cell: everything a reader needs, and the whole of what a commit
replaces atomically.

`next` is the allocation high-water mark. Every page at or above it is free, and
every page below it is either live or garbage left by an earlier commit. A
commit only ever writes at or above the *old* `next`, which is exactly why a
crash mid-commit cannot damage the tree the old root describes.
-/
structure Tree where
  /-- Page holding the root node, or `none` for an empty tree. -/
  root : Option Nat
  /-- First unallocated page. -/
  next : Nat
  deriving Inhabited, Repr, DecidableEq

/-- The empty tree, with page 0 reserved for the root cell itself. -/
def Tree.empty : Tree := { root := none, next := 1 }

/-- How a caller supplies page contents. -/
abbrev Pages := Nat → Option Node

/--
Read a page, refusing anything at or above the high-water mark.

This is the reader half of the discipline: even if a caller hands us a `Pages`
that happily returns half-written pages from a crashed commit, the tree will not
follow a pointer into that region.
-/
def Tree.get (t : Tree) (pages : Pages) (p : Nat) : Option Node :=
  if p < t.next then pages p else none

/-- Pages allocated so far by an in-progress update, and where the next one goes. -/
structure Alloc where
  next : Nat
  writes : List (Nat × Node)

/-- Place `n` in a fresh page. -/
def Alloc.push (a : Alloc) (n : Node) : Nat × Alloc :=
  (a.next, { next := a.next + 1, writes := a.writes ++ [(a.next, n)] })

end RaftKV.BTree

namespace RaftKV.BTree

open RaftKV

/-! ## Searching and updating

Every operation below allocates only through `Alloc.push`, which hands out pages
starting at the tree's current high-water mark and never below it. That is the
whole of the copy-on-write argument: an update writes a fresh copy of each node
on the path it touched, and the pages the *old* root reaches are untouched by
construction, not by an invariant anyone has to maintain.
-/

/-- Which child of a branch covers `k`: separators are the low key of the right side. -/
def childIndex (keys : Array Nat) (k : Nat) : Nat :=
  (keys.toList.filter (fun s => s ≤ k)).length

/-- Insert or replace `k` in a sorted record list. -/
def insertRec : List (Nat × ByteArray) → Nat → ByteArray → List (Nat × ByteArray)
  | [], k, v => [(k, v)]
  | (k', v') :: rs, k, v =>
      if k == k' then (k, v) :: rs
      else if k < k' then (k, v) :: (k', v') :: rs
      else (k', v') :: insertRec rs k v

/-- Drop `k` from a sorted record list. -/
def eraseRec : List (Nat × ByteArray) → Nat → List (Nat × ByteArray)
  | [], _ => []
  | (k', v') :: rs, k => if k == k' then rs else (k', v') :: eraseRec rs k

/-- Insert `x` at position `i`, clamped to the end. -/
def insAt {α : Type} : List α → Nat → α → List α
  | [], _, x => [x]
  | y :: ys, 0, x => x :: y :: ys
  | y :: ys, i + 1, x => y :: insAt ys i x

/-- Replace position `i`, or leave the list alone if it is out of range. -/
def setAt {α : Type} : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: ys, 0, x => x :: ys
  | y :: ys, i + 1, x => y :: setAt ys i x

/-- The outcome of updating one subtree. -/
inductive Ins where
  /-- The subtree still fits in one node, now living at this page. -/
  | ok (page : Nat)
  /-- It split: two pages and the separator that divides them. -/
  | split (left : Nat) (sep : Nat) (right : Nat)

/-- Halve an overfull leaf. -/
def splitLeaf (recs : List (Nat × ByteArray)) : Option (Node × Nat × Node) :=
  match recs.drop (recs.length / 2) with
  | [] => none
  | r :: rs => some (.leaf (recs.take (recs.length / 2)).toArray, r.1, .leaf (r :: rs).toArray)

/-- Halve an overfull branch, promoting the middle separator. -/
def splitBranch (keys : List Nat) (children : List Nat) : Option (Node × Nat × Node) :=
  let j := keys.length / 2
  match keys.drop j with
  | [] => none
  | sep :: right =>
      some (.branch (keys.take j).toArray (children.take (j + 1)).toArray,
            sep,
            .branch right.toArray (children.drop (j + 1)).toArray)

/-- Emit a node, splitting it first if it has grown past a page. -/
def emit (a : Alloc) (n : Node) (sp : Unit → Option (Node × Nat × Node)) :
    Option (Ins × Alloc) :=
  if fits n then
    let (q, a) := a.push n
    some (.ok q, a)
  else
    match sp () with
    | none => none
    | some (l, sep, r) =>
        if fits l && fits r then
          let (lq, a) := a.push l
          let (rq, a) := a.push r
          some (.split lq sep rq, a)
        else none

/-- The copy-on-write descent. `fuel` bounds the tree's depth. -/
def insertAux (t : Tree) (pages : Pages) (k : Nat) (v : ByteArray) :
    Nat → Nat → Alloc → Option (Ins × Alloc)
  | 0, _, _ => none
  | fuel + 1, p, a =>
      match t.get pages p with
      | none => none
      | some (.leaf recs) =>
          let recs' := insertRec recs.toList k v
          emit a (.leaf recs'.toArray) (fun _ => splitLeaf recs')
      | some (.branch keys children) =>
          let i := childIndex keys k
          match children[i]? with
          | none => none
          | some c =>
              match insertAux t pages k v fuel c a with
              | none => none
              | some (.ok q, a) =>
                  let ch := setAt children.toList i q
                  emit a (.branch keys ch.toArray)
                    (fun _ => splitBranch keys.toList ch)
              | some (.split lq sep rq, a) =>
                  let ks := insAt keys.toList i sep
                  let ch := insAt (setAt children.toList i lq) (i + 1) rq
                  emit a (.branch ks.toArray ch.toArray) (fun _ => splitBranch ks ch)

/-- Deepest tree this implementation will walk. -/
def maxDepth : Nat := 64

/--
Insert `k ↦ v`, returning the new root cell and the pages to write.

`none` means the value is too large for a page — the one input this
implementation rejects rather than handles.
-/
def Tree.insert (t : Tree) (pages : Pages) (k : Nat) (v : ByteArray) :
    Option (Tree × List (Nat × Node)) :=
  match t.root with
  | none =>
      let n := Node.leaf #[(k, v)]
      if fits n then
        let (q, a) := (Alloc.mk t.next []).push n
        some ({ root := some q, next := a.next }, a.writes)
      else none
  | some r =>
      match insertAux t pages k v maxDepth r ⟨t.next, []⟩ with
      | none => none
      | some (.ok q, a) => some ({ root := some q, next := a.next }, a.writes)
      | some (.split lq sep rq, a) =>
          let (nq, a) := a.push (.branch #[sep] #[lq, rq])
          some ({ root := some nq, next := a.next }, a.writes)

/-- Copy-on-write descent for deletion. Nodes are never merged or rebalanced. -/
def eraseAux (t : Tree) (pages : Pages) (k : Nat) :
    Nat → Nat → Alloc → Option (Nat × Alloc)
  | 0, _, _ => none
  | fuel + 1, p, a =>
      match t.get pages p with
      | none => none
      | some (.leaf recs) => some (a.push (.leaf (eraseRec recs.toList k).toArray))
      | some (.branch keys children) =>
          let i := childIndex keys k
          match children[i]? with
          | none => none
          | some c =>
              match eraseAux t pages k fuel c a with
              | none => none
              | some (q, a) =>
                  some (a.push (.branch keys (setAt children.toList i q).toArray))

/-- Remove `k`, returning the new root cell and the pages to write. -/
def Tree.erase (t : Tree) (pages : Pages) (k : Nat) : Option (Tree × List (Nat × Node)) :=
  match t.root with
  | none => some (t, [])
  | some r =>
      match eraseAux t pages k maxDepth r ⟨t.next, []⟩ with
      | none => none
      | some (q, a) => some ({ root := some q, next := a.next }, a.writes)

/-- Look `k` up. -/
def lookupAux (t : Tree) (pages : Pages) (k : Nat) : Nat → Nat → Option ByteArray
  | 0, _ => none
  | fuel + 1, p =>
      match t.get pages p with
      | none => none
      | some (.leaf recs) => (recs.toList.find? (fun r => r.1 == k)).map (fun r => r.2)
      | some (.branch keys children) =>
          match children[childIndex keys k]? with
          | none => none
          | some c => lookupAux t pages k fuel c

/-- The value bound to `k`, if any. -/
def Tree.lookup (t : Tree) (pages : Pages) (k : Nat) : Option ByteArray :=
  match t.root with
  | none => none
  | some r => lookupAux t pages k maxDepth r

/-- Every key in the tree, in order — used for scans and for testing. -/
def toListAux (t : Tree) (pages : Pages) : Nat → Nat → List (Nat × ByteArray)
  | 0, _ => []
  | fuel + 1, p =>
      match t.get pages p with
      | none => []
      | some (.leaf recs) => recs.toList
      | some (.branch _ children) =>
          children.toList.flatMap (fun c => toListAux t pages fuel c)

/-- All bindings, in key order. -/
def Tree.toList (t : Tree) (pages : Pages) : List (Nat × ByteArray) :=
  match t.root with
  | none => []
  | some r => toListAux t pages maxDepth r

end RaftKV.BTree
