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

/-- The abstract state of the store: a finite map, modelled as a function. -/
def KVModel := String → Option String

namespace KVModel

/-- The empty store binds no keys. -/
def empty : KVModel := fun _ => none

/-- Point update. -/
def insert (m : KVModel) (k : String) (v : String) : KVModel :=
  fun k' => if k' = k then some v else m k'

/-- Point removal. -/
def erase (m : KVModel) (k : String) : KVModel :=
  fun k' => if k' = k then none else m k'

/-- Lookup. -/
def find (m : KVModel) (k : String) : Option String := m k

end KVModel

/--
The sequential semantics of a single command: how the abstract state evolves
and what the client is told.
-/
def applyCmd (m : KVModel) : Command → KVModel × Reply
  | .get k     => (m, .value (m.find k))
  | .put k v   => (m.insert k v, .ok)
  | .del k     => (m.erase k, .ok)

/-- Fold `applyCmd` over a sequence of commands, discarding replies. -/
def applyAll (m : KVModel) : List Command → KVModel
  | []      => m
  | c :: cs => applyAll (applyCmd m c).1 cs

/-- The state reached by applying a command sequence to the empty store. -/
def run (cs : List Command) : KVModel := applyAll KVModel.empty cs

@[simp] theorem applyAll_nil (m : KVModel) : applyAll m [] = m := rfl

@[simp] theorem applyAll_cons (m : KVModel) (c : Command) (cs : List Command) :
    applyAll m (c :: cs) = applyAll (applyCmd m c).1 cs := rfl

/-- Applying a concatenation is applying each part in turn. -/
theorem applyAll_append (m : KVModel) (cs ds : List Command) :
    applyAll m (cs ++ ds) = applyAll (applyAll m cs) ds := by
  induction cs generalizing m with
  | nil => rfl
  | cons c cs ih => simp [applyAll, ih]

end RaftKV.Spec
