import RaftKV.Storage.BTree

open RaftKV RaftKV.BTree

/-! A page image store: what a file looks like, as a map from page number to bytes. -/
abbrev Image := Nat → Option ByteArray

def empty : Image := fun _ => none

def Image.set (img : Image) (p : Nat) (bs : ByteArray) : Image :=
  fun q => if q == p then some bs else img q

def Image.pages (img : Image) : Pages := fun p =>
  match img p with
  | none => none
  | some bs => decodePage p bs

/-- Apply a commit's writes to the image. -/
def commit (img : Image) (ws : List (Nat × Node)) : Option Image :=
  ws.foldl (fun acc (w : Nat × Node) =>
    match acc, encodePage w.1 w.2 with
    | some img, some bs => some (img.set w.1 bs)
    | _, _ => none) (some img)

/-- Values large enough that the test trees are several levels deep. -/
def val (k : Nat) : ByteArray := String.toUTF8 (s!"value-{k}-" ++ String.ofList (List.replicate 180 'x'))

/-- Insert a batch of keys, committing each one. -/
def insertAll (t : Tree) (img : Image) : List Nat → Option (Tree × Image)
  | [] => some (t, img)
  | k :: ks =>
      match t.insert img.pages k (val k) with
      | none => none
      | some (t', ws) =>
          match commit img ws with
          | none => none
          | some img' => insertAll t' img' ks

def keys : List Nat := (List.range 400).map (fun i => (i * 37) % 400)

/-! ## Page-level checks -/

#eval do
  let some bs := encodePage 7 (.leaf #[(1, String.toUTF8 "a")]) | throw (IO.userError "encode")
  IO.println s!"page size {bs.size} (want {pageSize})"
  IO.println s!"round-trips: {(decodePage 7 bs).isSome}"
  -- a single flipped bit in the payload
  let torn := bs.set! 100 (bs.get! 100 ^^^ 1)
  IO.println s!"bit flip rejected: {(decodePage 7 torn).isNone}"
  -- the tail of the page never made it to the platter. A page whose tail is all
  -- padding would survive this unchanged, and rightly so, so tear a full one.
  let big : Node := .leaf ((List.range 120).map (fun i => (i, String.toUTF8 s!"value-{i}-padding-padding"))).toArray
  let some bb := encodePage 7 big | throw (IO.userError "encode big")
  IO.println s!"full page body bytes: {(ByteCodec.enc big).length}"
  let torn2 := (bb.extract 0 2048) ++ ByteArray.mk (Array.replicate 2048 (0 : UInt8))
  IO.println s!"torn write rejected: {(decodePage 7 torn2).isNone}"
  -- and the sector-sized granularity a drive actually writes in
  let torn3 := (bb.extract 0 3584) ++ ByteArray.mk (Array.replicate 512 (0xff : UInt8))
  IO.println s!"lost final sector rejected: {(decodePage 7 torn3).isNone}"
  -- a valid page, but the wrong one
  IO.println s!"misdirected read rejected: {(decodePage 8 bs).isNone}"

/-! ## Tree-level checks -/

#eval do
  let some (t, img) := insertAll Tree.empty (empty) keys
    | throw (IO.userError "insert failed")
  IO.println s!"pages allocated: {t.next}, root {t.root}"
  let found := keys.all (fun k => t.lookup img.pages k == some (val k))
  IO.println s!"all keys found: {found}"
  let absent := ((List.range 50).map (· + 1000)).all (fun k => (t.lookup img.pages k).isNone)
  IO.println s!"absent keys absent: {absent}"
  let l := t.toList img.pages
  IO.println s!"scan size {l.length}, sorted: {(l.map Prod.fst) == (List.range 400)}"

/-! ## Copy-on-write: an old root still sees the old tree -/

#eval do
  let some (t1, img1) := insertAll Tree.empty (empty) (List.range 200)
    | throw (IO.userError "insert failed")
  let some (t2, img2) := insertAll t1 img1 ((List.range 200).map (· + 200))
    | throw (IO.userError "insert failed")
  -- the *old* root cell, reading the *new* image: none of its pages moved
  IO.println s!"old root over new image: {(t1.toList img2.pages).length} (want 200)"
  IO.println s!"new root over new image: {(t2.toList img2.pages).length} (want 400)"
  let overwritten := (List.range t1.next).any (fun p =>
    match img1 p, img2 p with
    | some a, some b => a != b
    | _, _ => false)
  IO.println s!"any live page overwritten: {overwritten} (want false)"

/-! ## Deletion -/

#eval do
  let some (t, img) := insertAll Tree.empty (empty) (List.range 300)
    | throw (IO.userError "insert failed")
  let step : Option (Tree × Image) → Nat → Option (Tree × Image) := fun acc k =>
    match acc with
    | none => none
    | some (t, img) =>
        match t.erase img.pages k with
        | none => none
        | some (t', ws) => (commit img ws).map (fun i => (t', i))
  let some (t', img') := ((List.range 300).filter (· % 3 == 0)).foldl step (some (t, img))
    | throw (IO.userError "erase failed")
  let l := t'.toList img'.pages
  IO.println s!"after deleting every third: {l.length} (want 200)"
  IO.println s!"survivors correct: {(l.map Prod.fst) == (List.range 300).filter (· % 3 != 0)}"

/-! ## Crash points

`RaftKV.Storage.Persist` proves that a crash at any point in the commit sequence
recovers either the old value or the new one. Here is the same statement
exercised concretely on the B-tree: for every prefix of a commit's page writes,
with the root cell not yet swapped, the *old* root must still read exactly the
tree it read before — and with all the writes and the swap, the new one must
read the updated tree.

The pages a crash can have half-written are all at or above the old high-water
mark, so this is testing the property the design is built on rather than hoping
for it: garbage is written over every unwritten page in the commit's range to
make sure nothing live is being relied on there.
-/

#eval do
  let some (t, img) := insertAll Tree.empty empty (List.range 300)
    | throw (IO.userError "setup failed")
  IO.println s!"crash-point tree: {t.next} pages, root {t.root}"
  let before := t.toList img.pages
  let some (t', ws) := t.insert img.pages 1000 (val 1000)
    | throw (IO.userError "insert failed")
  let mut allOld := true
  for n in List.range (ws.length + 1) do
    -- the commit got `n` pages out before the crash; every other page in the
    -- range it was allocating holds whatever was there, modelled as garbage
    let some partial_ := commit img (ws.take n)
      | throw (IO.userError "commit failed")
    let scribbled : Image := fun p =>
      if t.next ≤ p && p < t'.next && (ws.take n).all (fun w => w.1 != p) then
        some (ByteArray.mk (Array.replicate pageSize (0xa5 : UInt8)))
      else partial_ p
    -- the old root cell is still the live one: it must see the old tree
    if t.toList scribbled.pages != before then allOld := false
    if t.lookup scribbled.pages 42 != some (val 42) then allOld := false
  IO.println s!"old root intact at all {ws.length + 1} crash points: {allOld}"
  let some after := commit img ws | throw (IO.userError "commit failed")
  IO.println s!"new root after the swap: {(t'.toList after.pages).length} (want 301)"
  IO.println s!"and the new key is there: {t'.lookup after.pages 1000 == some (val 1000)}"
