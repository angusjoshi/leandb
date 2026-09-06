import RaftKV.Storage.KV
import Std.Data.HashMap

/-!
# `Std.HashMap` as the state-machine map

The simple implementation. Replacing it with a persistent map costs exactly the
`LawfulKVStore` instance below.
-/

namespace RaftKV

open Spec Std

/-- A key/value state machine backed by a hash map. -/
structure HashKV where
  /-- The underlying map. -/
  map : HashMap String String
  deriving Inhabited

namespace HashKV

instance : KVStore HashKV where
  empty := ⟨∅⟩
  find m k := m.map[k]?
  insert m k v := ⟨m.map.insert k v⟩
  erase m k := ⟨m.map.erase k⟩

instance : LawfulKVStore HashKV where
  toModel m := fun k => m.map[k]?
  model_empty := by
    funext k; simp [KVStore.empty, KVModel.empty]
  model_find := by
    intro m k; rfl
  model_insert := by
    intro m k v
    funext k'
    simp only [KVStore.insert, KVModel.insert, HashMap.getElem?_insert]
    by_cases h : k' = k
    · simp [h]
    · simp [h, Ne.symm h]
  model_erase := by
    intro m k
    funext k'
    simp only [KVStore.erase, KVModel.erase, HashMap.getElem?_erase]
    by_cases h : k' = k
    · simp [h]
    · simp [h, Ne.symm h]

end HashKV

end RaftKV
