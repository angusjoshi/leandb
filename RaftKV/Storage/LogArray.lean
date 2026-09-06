import RaftKV.Storage.Log

/-!
# `ArrayLog`: the simple, in-memory log implementation

The first inhabitant of `LogStore`. It is deliberately unsophisticated — a flat
`Array Entry` — because its job is to make the system run while the proofs are
developed against the *interface*, not against it.

The whole cost of replacing it later with a segmented, memory-mapped log is
reproducing the `LawfulLogStore ArrayLog` instance below. Nothing in
`RaftKV.Protocol` or `RaftKV.Proof` mentions `ArrayLog`.
-/

namespace RaftKV

/-- A log backed by a contiguous array. Entry at 1-based index `i` is `entries[i-1]`. -/
structure ArrayLog where
  /-- The entries, in log order. -/
  entries : Array Entry
  deriving Inhabited, Repr, DecidableEq

namespace ArrayLog

instance : LogStore ArrayLog where
  empty := ⟨#[]⟩
  append s e := ⟨s.entries.push e⟩
  get s i := if i = 0 then none else s.entries[i - 1]?
  truncFrom s i := ⟨s.entries.extract 0 (i - 1)⟩
  size s := s.entries.size
  sliceFrom s i := (s.entries.extract (i - 1) s.entries.size).toList

instance : LawfulLogStore ArrayLog where
  toModel s := s.entries.toList
  model_empty := rfl
  model_append := by intro s e; simp [LogStore.append]
  model_get := by
    intro s i
    by_cases hi : i = 0 <;> simp [LogStore.get, hi]
  model_truncFrom := by
    intro s i
    simp [LogStore.truncFrom]
  model_size := by intro s; simp [LogStore.size]
  model_sliceFrom := by
    intro s i
    simp only [LogStore.sliceFrom, Array.toList_extract, List.extract_eq_take_drop]
    exact List.take_of_length_le (by simp)

end ArrayLog

end RaftKV
