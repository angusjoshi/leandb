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
  toPairs m := m.map.toList
  ofPairs l := ⟨HashMap.ofList l⟩

instance : LawfulKVStore HashKV where
  toModel m := fun k => m.map[k]?
  model_empty := by
    funext k; simp [KVStore.empty, Map.empty]
  model_find := by
    intro m k; rfl
  model_insert := by
    intro m k v
    funext k'
    simp only [KVStore.insert, Map.insert, HashMap.getElem?_insert]
    by_cases h : k' = k
    · simp [h]
    · simp [h, Ne.symm h]
  model_erase := by
    intro m k
    funext k'
    simp only [KVStore.erase, Map.erase, HashMap.getElem?_erase]
    by_cases h : k' = k
    · simp [h]
    · simp [h, Ne.symm h]
  model_pairs := by
    intro m
    funext k
    show (HashMap.ofList m.map.toList)[k]? = m.map[k]?
    cases hq : m.map[k]? with
    | some v =>
        have hmem : (k, v) ∈ m.map.toList := HashMap.mem_toList_iff_getElem?_eq_some.mpr hq
        exact HashMap.getElem?_insertMany_list_of_mem (by simp)
          HashMap.distinct_keys_toList hmem
    | none =>
        have hc : (m.map.toList.map Prod.fst).contains k = false := by
          rcases hcc : (m.map.toList.map Prod.fst).contains k with _ | _
          · rfl
          · exfalso
            obtain ⟨p, hp, hpk⟩ := List.mem_map.mp (List.mem_of_elem_eq_true hcc)
            have hg : m.map[p.1]? = some p.2 := HashMap.mem_toList_iff_getElem?_eq_some.mp hp
            rw [hpk, hq] at hg
            exact absurd hg (by simp)
        have hi := HashMap.getElem?_insertMany_list_of_contains_eq_false
          (m := (∅ : HashMap String String)) hc
        rw [show HashMap.ofList m.map.toList
          = (∅ : HashMap String String).insertMany m.map.toList from rfl, hi]
        simp

end HashKV

end RaftKV
