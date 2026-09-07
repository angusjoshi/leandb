import RaftKV.Spec.KV

/-!
# The state-machine map, abstractly

Same two-class pattern as `RaftKV.LogStore`: `KVStore` holds the executable
operations, `LawfulKVStore` holds the refinement mapping into `Spec.KVModel`
plus the laws.

The anticipated replacement here is a persistent / copy-on-write map, which
makes snapshotting a leader's state machine cheap (snapshot = keep the old
root). Note that the interface below never exposes iteration or a size, so a
structurally-shared implementation satisfies it without difficulty.
-/

namespace RaftKV

open Spec

/-- Executable operations of the replicated state machine's map. -/
class KVStore (κ : Type) where
  /-- The map binding no keys. -/
  empty : κ
  /-- Look up a key. -/
  find : κ → String → Option String
  /-- Bind a key to a value, replacing any existing binding. -/
  insert : κ → String → String → κ
  /-- Remove a key's binding, if any. -/
  erase : κ → String → κ
  /--
  Serialise the map's bindings. Log compaction forces this on the interface:
  discarding a prefix of the log means a restart cannot replay it, so the state
  machine at the compaction point has to be written down.
  -/
  toPairs : κ → List (String × String)
  /-- Rebuild a map from serialised bindings. -/
  ofPairs : List (String × String) → κ

/--
The refinement mapping into the abstract `Spec.Map`, plus its laws.

`model_find` is the important one: it says the *observable* result of a lookup
on the implementation agrees with the specification. The other three say the
implementation's state transitions track the specification's.
-/
class LawfulKVStore (κ : Type) [KVStore κ] where
  /-- The abstract contents of the map. Proof-level only. -/
  toModel : κ → Map
  model_empty : toModel (KVStore.empty : κ) = Map.empty
  model_find : ∀ (m : κ) (k : String), KVStore.find m k = (toModel m).find k
  model_insert : ∀ (m : κ) (k v : String),
    toModel (KVStore.insert m k v) = (toModel m).insert k v
  model_erase : ∀ (m : κ) (k : String),
    toModel (KVStore.erase m k) = (toModel m).erase k
  /-- Serialising and rebuilding preserves what the map means. -/
  model_pairs : ∀ (m : κ),
    toModel (KVStore.ofPairs (KVStore.toPairs m) : κ) = toModel m

export LawfulKVStore (model_empty model_find model_insert model_erase model_pairs)

namespace KVStore

/-! The transition function itself takes only `[KVStore κ]`, so it stays
executable independently of the lawful instance. -/

variable {κ : Type} [KVStore κ]

/-- Executable command application: the state machine's transition function. -/
def applyCmd (m : κ) : Command → κ × Reply
  | .get k   => (m, .value (find m k))
  | .put k v => (insert m k v, .ok)
  | .del k   => (erase m k, .ok)

section Lawful

variable [LawfulKVStore κ]

/--
**The state machine refines its specification.**

Applying a command to a lawful implementation produces the reply the
specification demands, and lands in a state modelling the specification's next
state. Proved once here; every `KVStore` instance inherits it.
-/
theorem applyCmd_refines (m : κ) (c : Command) :
    LawfulKVStore.toModel (applyCmd m c).1 = (Spec.applyCmd (LawfulKVStore.toModel m) c).1
      ∧ (applyCmd m c).2 = (Spec.applyCmd (LawfulKVStore.toModel m) c).2 := by
  cases c with
  | get k => exact ⟨rfl, by simp [applyCmd, Spec.applyCmd, model_find]⟩
  | put k v => exact ⟨model_insert m k v, rfl⟩
  | del k => exact ⟨model_erase m k, rfl⟩

/-- Corollary: replies always match the specification. -/
theorem applyCmd_reply (m : κ) (c : Command) :
    (applyCmd m c).2 = (Spec.applyCmd (LawfulKVStore.toModel m) c).2 :=
  (applyCmd_refines m c).2

/-- Corollary: states always match the specification. -/
theorem applyCmd_state (m : κ) (c : Command) :
    LawfulKVStore.toModel (applyCmd m c).1 = (Spec.applyCmd (LawfulKVStore.toModel m) c).1 :=
  (applyCmd_refines m c).1

/-- Folding commands through the implementation tracks folding them through the spec. -/
theorem applyAll_refines (m : κ) (cs : List Command) :
    LawfulKVStore.toModel (cs.foldl (fun s c => (applyCmd s c).1) m)
      = Spec.applyAll (LawfulKVStore.toModel m) cs := by
  induction cs generalizing m with
  | nil => rfl
  | cons c cs ih => simp [Spec.applyAll, ← applyCmd_state, ih]

end Lawful

end KVStore

end RaftKV
