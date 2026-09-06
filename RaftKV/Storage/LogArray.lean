import RaftKV.Storage.Log

/-!
# `ArrayLog`: the simple, in-memory log implementation

The first inhabitant of `LogStore`. A flat `Array Entry` plus a **base offset**:
the array holds the entries from `base + 1` onwards, and compaction drops the
prefix instead of keeping holes for it. That is the whole point — the model
pretends discarded entries are still there as `none`, precisely so the
implementation does not have to keep anything at all.

Compaction is an `Array.extract`, so it is linear in what survives and does not
copy what it discards twice.

The whole cost of replacing this with a segmented or B-tree-backed log is
reproducing the `LawfulLogStore ArrayLog` instance below. Nothing in
`RaftKV.Protocol` or `RaftKV.Proof` mentions `ArrayLog`.
-/

namespace RaftKV

/--
A log backed by a contiguous array.

`entries[j]` is the entry at 1-based log index `base + 1 + j`; everything at or
below `base` has been compacted away.
-/
structure ArrayLog where
  /-- Number of entries discarded from the front. -/
  base : Nat
  /-- The entries still held, in log order. -/
  entries : Array Entry
  deriving Inhabited, Repr, DecidableEq

namespace ArrayLog

instance : LogStore ArrayLog where
  empty := ⟨0, #[]⟩
  append s e := ⟨s.base, s.entries.push e⟩
  get s i := if i ≤ s.base then none else s.entries[i - s.base - 1]?
  truncFrom s i :=
    if i - 1 ≤ s.base then ⟨i - 1, #[]⟩ else ⟨s.base, s.entries.extract 0 (i - 1 - s.base)⟩
  size s := s.base + s.entries.size
  sliceFrom s i := (s.entries.extract (i - s.base - 1) s.entries.size).toList
  firstIndex s := s.base + 1
  compact s i :=
    let j := max (s.base + 1) (min i (s.base + s.entries.size))
    ⟨j - 1, s.entries.extract (j - 1 - s.base) s.entries.size⟩
  fromAnchor i e := ⟨i - 1, #[e]⟩

/-- The model: a hole for every discarded index, then the entries held. -/
def model (s : ArrayLog) : List (Option Entry) :=
  List.replicate s.base none ++ s.entries.toList.map some

theorem get_eq (s : ArrayLog) (i : Nat) :
    LogStore.get s i = if i ≤ s.base then none else s.entries[i - s.base - 1]? := rfl

theorem model_get_aux (s : ArrayLog) (i : Nat) (hi : i ≠ 0) :
    ((model s)[i - 1]?).join = if i ≤ s.base then none else s.entries[i - s.base - 1]? := by
  have hrep : (List.replicate s.base (none : Option Entry)).length = s.base :=
    List.length_replicate ..
  unfold model
  by_cases hb : i ≤ s.base
  · rw [if_pos hb, List.getElem?_append_left (by omega), List.getElem?_replicate,
      if_pos (by omega)]
    rfl
  · rw [if_neg hb, List.getElem?_append_right (by omega), List.getElem?_map]
    have harg : i - 1 - s.base = i - s.base - 1 := by omega
    rw [hrep, harg, Array.getElem?_toList]
    cases s.entries[i - s.base - 1]? <;> rfl

instance : LawfulLogStore ArrayLog where
  toModel := model
  model_empty := rfl
  model_append := by
    intro s e
    show model ⟨s.base, s.entries.push e⟩ = model s ++ [some e]
    unfold model
    simp [List.append_assoc]
  model_get := by
    intro s i
    by_cases hi : i = 0
    · subst hi; rw [if_pos rfl, get_eq, if_pos (Nat.zero_le _)]
    · rw [if_neg hi, get_eq, model_get_aux s i hi]
  model_truncFrom := by
    intro s i
    have hrep : (List.replicate s.base (none : Option Entry)).length = s.base :=
      List.length_replicate ..
    show model (if i - 1 ≤ s.base then ⟨i - 1, #[]⟩ else
      ⟨s.base, s.entries.extract 0 (i - 1 - s.base)⟩) = (model s).take (i - 1)
    by_cases hb : i - 1 ≤ s.base
    · rw [if_pos hb]
      unfold model
      rw [List.take_append, hrep, Nat.sub_eq_zero_of_le hb]
      simp only [Array.toList_empty, List.map_nil, List.append_nil, List.take_replicate,
        List.take_zero]
      congr 1
      omega
    · rw [if_neg hb]
      unfold model
      rw [List.take_append, hrep, List.take_replicate, Nat.min_eq_right (by omega)]
      simp only [Array.toList_extract, List.extract_eq_take_drop, List.drop_zero,
        Nat.sub_zero]
      congr 1
      rw [List.map_take]
  model_size := by intro s; simp [model, LogStore.size]
  model_sliceFrom := by
    intro s i hi
    show ((s.entries.extract (i - s.base - 1) s.entries.size).toList).map some
      = (model s).drop (i - 1)
    have hrep : (List.replicate s.base (none : Option Entry)).length = s.base :=
      List.length_replicate ..
    have hi' : s.base + 1 ≤ i := hi
    clear hi
    have harg : i - s.base - 1 = i - 1 - s.base := by omega
    unfold model
    rw [List.drop_append, hrep, List.drop_eq_nil_of_le (by simp; omega)]
    simp only [Array.toList_extract, List.extract_eq_take_drop, List.nil_append]
    rw [List.take_of_length_le (by simp), harg, List.map_drop]
  model_compact := by
    intro s i h1 h2
    have hi' : s.base + 1 ≤ i := h1
    have hi2 : i ≤ s.base + s.entries.size := h2
    have hj : max (s.base + 1) (min i (s.base + s.entries.size)) = i := by omega
    have hrep : (List.replicate s.base (none : Option Entry)).length = s.base :=
      List.length_replicate ..
    show model ⟨_ - 1, s.entries.extract (_ - 1 - s.base) s.entries.size⟩
      = List.replicate (i - 1) none ++ (model s).drop (i - 1)
    have harg : i - 1 - s.base = i - 1 - s.base := rfl
    rw [hj]
    unfold model
    rw [List.drop_append, hrep, List.drop_eq_nil_of_le (by simp; omega)]
    simp only [Array.toList_extract, List.extract_eq_take_drop, List.nil_append]
    rw [List.take_of_length_le (by simp), List.map_drop]
  first_pos := by intro s; exact Nat.succ_le_succ (Nat.zero_le _)
  get_lt_first := by
    intro s k hk
    have hk' : k < s.base + 1 := hk
    show (if k ≤ s.base then none else _) = none
    rw [if_pos (by omega)]
  get_isSome := by
    intro s k h1 h2
    have h1' : s.base + 1 ≤ k := h1
    have h2' : k ≤ s.base + s.entries.size := h2
    show (if k ≤ s.base then none else s.entries[k - s.base - 1]?).isSome = true
    rw [if_neg (by omega)]
    rw [Array.getElem?_eq_getElem (by omega)]
    rfl
  first_empty := rfl
  first_append := by intro s e; rfl
  first_truncFrom := by
    intro s i
    show (if i - 1 ≤ s.base then (⟨i - 1, #[]⟩ : ArrayLog) else _).base + 1
      = max 1 (min (s.base + 1) i)
    by_cases hb : i - 1 ≤ s.base
    · rw [if_pos hb]; show i - 1 + 1 = _; omega
    · rw [if_neg hb]; show s.base + 1 = _; omega
  model_fromAnchor := by
    intro i e
    show model ⟨i - 1, #[e]⟩ = _
    rfl
  first_fromAnchor := by
    intro i e
    show i - 1 + 1 = max 1 i
    omega
  first_compact := by
    intro s i h1 h2
    have hi' : s.base + 1 ≤ i := h1
    have hi2 : i ≤ s.base + s.entries.size := h2
    show (max (s.base + 1) (min i (s.base + s.entries.size))) - 1 + 1 = i
    omega

end ArrayLog

end RaftKV
