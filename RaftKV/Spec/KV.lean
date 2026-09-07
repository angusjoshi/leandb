import RaftKV.Core.Types

/-!
# Sequential key/value specification

This is the top of the refinement chain: the single-node, no-failures meaning
of the store. Every claim about the distributed system is ultimately a claim
that its externally visible behaviour matches *this*.

The state is a plain total function `String → Option String`. That is a
deliberately impractical representation: it is here to be reasoned about, never
to be executed. Executable maps live behind `RaftKV.Storage.KVStore` and are
related back to this model by that class's laws.
-/

namespace RaftKV.Spec

/-- The abstract contents of the store: a finite map, modelled as a function. -/
def Map := String → Option String

namespace Map

/-- The empty store binds no keys. -/
def empty : Map := fun _ => none

/-- Point update. -/
def insert (m : Map) (k : String) (v : String) : Map :=
  fun k' => if k' = k then some v else m k'

/-- Point removal. -/
def erase (m : Map) (k : String) : Map :=
  fun k' => if k' = k then none else m k'

/-- Lookup. -/
def find (m : Map) (k : String) : Option String := m k

end Map

/--
The sequential semantics of a single command: how the abstract state evolves
and what the client is told.
-/
def applyCmd (m : Map) : Command → Map × Reply
  | .get k     => (m, .value (m.find k))
  | .put k v   => (m.insert k v, .ok)
  | .del k     => (m.erase k, .ok)

/-- Fold `applyCmd` over a sequence of commands, discarding replies. -/
def applyAll (m : Map) : List Command → Map
  | []      => m
  | c :: cs => applyAll (applyCmd m c).1 cs

/-- The state reached by applying a command sequence to the empty store. -/
def run (cs : List Command) : Map := applyAll Map.empty cs

@[simp] theorem applyAll_nil (m : Map) : applyAll m [] = m := rfl

@[simp] theorem applyAll_cons (m : Map) (c : Command) (cs : List Command) :
    applyAll m (c :: cs) = applyAll (applyCmd m c).1 cs := rfl

/-- Applying a concatenation is applying each part in turn. -/
theorem applyAll_append (m : Map) (cs ds : List Command) :
    applyAll m (cs ++ ds) = applyAll (applyAll m cs) ds := by
  induction cs generalizing m with
  | nil => rfl
  | cons c cs ih => simp [applyAll, ih]

/-! ## Exactly once

A client that is refused, or whose reply is lost, retries with the same request
id. Without duplicate suppression its command can commit twice, under two
indices, and be applied twice — which for a `put` is harmless and for a `del`
followed by someone else's `put` is not. So the specification itself remembers
which requests it has already carried out.

Only *writes* are remembered. A read has no effect, so re-executing a retried
read against the state at the retry is not a duplicated operation at all — it is
a second operation, correctly linearized where it lands. Suppressing it would
make the answer stale, which is worse.

The state is therefore the map together with the set of write requests already
performed, and both are what a replica's state machine holds.
-/

/-- Which requests have already been carried out. -/
abbrev Seen := Nat → Bool

/-- The abstract state of the store: its contents, and what it has already done. -/
structure KVModel where
  /-- The bindings. -/
  map : Map
  /-- The write requests already performed. -/
  seen : Seen

/-- The empty store binds no keys and has done nothing. -/
def KVModel.empty : KVModel := ⟨Map.empty, fun _ => false⟩

/-- Is this command a write? Only writes are remembered. -/
def isWrite : Command → Bool
  | .get _ => false
  | _ => true

/--
The sequential semantics of one *log entry*: the command, and the request id it
came from.

A write whose request has already been performed is not performed again, and the
client is told `ok` — the same answer it would have had the first time, because
that is the only answer a write ever has.
-/
def applyEntry (m : KVModel) (e : Entry) : KVModel × Reply :=
  if isWrite e.cmd && m.seen e.reqId then (m, .ok)
  else
    let (m', r) := applyCmd m.map e.cmd
    (⟨m', fun q => m.seen q || (isWrite e.cmd && q == e.reqId)⟩, r)

/-- Fold `applyEntry` over a sequence of entries, discarding replies. -/
def applyAllE (m : KVModel) : List Entry → KVModel
  | []      => m
  | e :: es => applyAllE (applyEntry m e).1 es

/-- The state reached by applying a log to the empty store. -/
def runE (es : List Entry) : KVModel := applyAllE KVModel.empty es

@[simp] theorem applyAllE_nil (m : KVModel) : applyAllE m [] = m := rfl

@[simp] theorem applyAllE_cons (m : KVModel) (e : Entry) (es : List Entry) :
    applyAllE m (e :: es) = applyAllE (applyEntry m e).1 es := rfl

/-- Applying a concatenation is applying each part in turn. -/
theorem applyAllE_append (m : KVModel) (es fs : List Entry) :
    applyAllE m (es ++ fs) = applyAllE (applyAllE m es) fs := by
  induction es generalizing m with
  | nil => rfl
  | cons e es ih => simp [applyAllE, ih]

end RaftKV.Spec
