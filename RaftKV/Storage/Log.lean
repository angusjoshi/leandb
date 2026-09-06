import RaftKV.Core.Types

/-!
# The replicated log, abstractly

This is the project's flagship abstraction and sets the pattern every other
swappable component follows.

`LogStore` carries **operations only** and is computable. `LawfulLogStore`
carries the refinement mapping `toModel : σ → List Entry` together with laws
saying each operation commutes with it.

The split matters for more than tidiness. A future segmented, memory-mapped log
cannot *compute* its full contents as a `List Entry` without paging the entire
log into memory. Because `toModel` lives in the lawful class, such an instance
may be `noncomputable` while the operational instance stays fully executable.
Proofs mention `toModel`; compiled code cannot.

Note also what is *absent*: there is no `toList` operation. Materialising the
whole log is a proof-level fiction, never something the running system does.
Reads are `get` (one entry) and `sliceFrom` (a bounded suffix), both of which a
segmented log implements cheaply.

Indices are 1-based: `get s 0 = none` always.
-/

namespace RaftKV

/-- Executable operations of a Raft log. -/
class LogStore (σ : Type) where
  /-- The empty log. -/
  empty : σ
  /-- Append one entry at the end, giving it index `size + 1`. -/
  append : σ → Entry → σ
  /-- Fetch the entry at a 1-based index, or `none` if out of range. -/
  get : σ → Nat → Option Entry
  /-- Delete every entry at index `≥ i`, keeping the prefix of length `i - 1`. -/
  truncFrom : σ → Nat → σ
  /-- Number of entries; equivalently the highest valid index. -/
  size : σ → Nat
  /-- Every entry at index `≥ i`, in order. Bounded: used to fill `AppendEntries`. -/
  sliceFrom : σ → Nat → List Entry

/--
The refinement mapping from a log implementation to its mathematical model,
plus the laws that make it a refinement.

Proving these six laws is the *entire* cost of swapping in a new log
implementation. Every theorem in `RaftKV.Proof` is stated over `toModel` and so
transports to any lawful instance unchanged.
-/
class LawfulLogStore (σ : Type) [LogStore σ] where
  /-- The abstract contents of the log. Proof-level only. -/
  toModel : σ → List Entry
  model_empty : toModel (LogStore.empty : σ) = []
  model_append : ∀ (s : σ) (e : Entry),
    toModel (LogStore.append s e) = toModel s ++ [e]
  model_get : ∀ (s : σ) (i : Nat),
    LogStore.get s i = if i = 0 then none else (toModel s)[i - 1]?
  model_truncFrom : ∀ (s : σ) (i : Nat),
    toModel (LogStore.truncFrom s i) = (toModel s).take (i - 1)
  model_size : ∀ (s : σ), LogStore.size s = (toModel s).length
  model_sliceFrom : ∀ (s : σ) (i : Nat),
    LogStore.sliceFrom s i = (toModel s).drop (i - 1)

export LawfulLogStore (toModel model_empty model_append model_get model_truncFrom
  model_size model_sliceFrom)

attribute [simp] model_empty model_append model_size

namespace LogStore

/-! Derived *operations*. These take only `[LogStore σ]`: they must remain
executable, so they may not depend on the lawful instance. -/

variable {σ : Type} [LogStore σ]

/-- The index of the last entry; `0` when the log is empty. -/
def lastIndex (s : σ) : Nat := size s

/-- The term of the entry at index `i`, if that entry exists. -/
def termAt (s : σ) (i : Nat) : Option Nat := (get s i).map Entry.term

/-- The term of the last entry; `0` for an empty log, which is below every real term. -/
def lastTerm (s : σ) : Nat := (termAt s (lastIndex s)).getD 0

end LogStore

/-! ## Derived facts

Proved once from the laws, available to every implementation forever. This is
what "composable proofs" buys: the lemmas below never mention a concrete log.
-/

namespace LogStore

variable {σ : Type} [LogStore σ] [LawfulLogStore σ]

@[simp] theorem get_zero (s : σ) : get s 0 = none := by
  simp [model_get]

@[simp] theorem lastIndex_empty : lastIndex (empty : σ) = 0 := by
  simp [lastIndex]

theorem lastIndex_append (s : σ) (e : Entry) :
    lastIndex (append s e) = lastIndex s + 1 := by
  simp [lastIndex]

/-- An index is valid exactly when it is between `1` and `lastIndex`. -/
theorem get_isSome_iff (s : σ) (i : Nat) :
    (get s i).isSome ↔ 1 ≤ i ∧ i ≤ lastIndex s := by
  rw [model_get]
  by_cases hi : i = 0
  · simp [hi]
  · have hi' : 1 ≤ i := Nat.pos_of_ne_zero hi
    simp only [hi, if_false, lastIndex, model_size]
    rw [Option.isSome_iff_ne_none, ne_eq, List.getElem?_eq_none_iff]
    omega

/-- Appending never disturbs an entry that already existed. -/
theorem get_append_of_le (s : σ) (e : Entry) (i : Nat) (h : i ≤ lastIndex s) :
    get (append s e) i = get s i := by
  rw [model_get, model_get, model_append]
  by_cases hi : i = 0
  · simp [hi]
  · have hi' : 1 ≤ i := Nat.pos_of_ne_zero hi
    simp only [lastIndex, model_size] at h
    simp only [hi, if_false]
    exact List.getElem?_append_left (by omega)

/-- The freshly appended entry sits at the new last index. -/
@[simp] theorem get_append_self (s : σ) (e : Entry) :
    get (append s e) (lastIndex s + 1) = some e := by
  rw [model_get]
  simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, model_append]
  rw [List.getElem?_append_right (by simp [lastIndex, model_size])]
  simp [lastIndex, model_size]

/-- Truncation cannot lengthen the log. -/
theorem lastIndex_truncFrom_le (s : σ) (i : Nat) :
    lastIndex (truncFrom s i) ≤ lastIndex s := by
  simp only [lastIndex, model_size, model_truncFrom, List.length_take]
  exact Nat.min_le_right _ _

/-- Truncating at `i` leaves every entry below `i` untouched. -/
theorem get_truncFrom_of_lt (s : σ) (i j : Nat) (h : j < i) :
    get (truncFrom s i) j = get s j := by
  rw [model_get, model_get, model_truncFrom]
  by_cases hj : j = 0
  · simp [hj]
  · have hj' : 1 ≤ j := Nat.pos_of_ne_zero hj
    simp only [hj, if_false]
    exact List.getElem?_take_of_lt (by omega)

/-- Truncation leaves exactly the prefix below `i`, capped by the log's length. -/
theorem lastIndex_truncFrom (s : σ) (i : Nat) :
    lastIndex (truncFrom s i) = min (i - 1) (lastIndex s) := by
  simp only [lastIndex, model_size, model_truncFrom, List.length_take]

/-- Truncating at `i` when the log reaches `i` leaves exactly `i - 1` entries. -/
theorem lastIndex_truncFrom_of_le (s : σ) (i : Nat) (h : i ≤ lastIndex s) :
    lastIndex (truncFrom s i) = i - 1 := by
  rw [lastIndex_truncFrom]; omega

/-- Complete description of `get` after an append. -/
theorem get_append (s : σ) (e : Entry) (k : Nat) :
    get (append s e) k = if k = lastIndex s + 1 then some e else get s k := by
  rw [model_get, model_get, model_append]
  by_cases hk : k = 0
  · subst hk; simp [lastIndex, model_size]
  · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk
    have hlen : lastIndex s = (toModel s).length := by simp [lastIndex, model_size]
    simp only [hk, if_false, List.getElem?_append]
    by_cases hlt : k - 1 < (toModel s).length
    · rw [if_pos hlt, if_neg (by omega)]
    · rw [if_neg hlt]
      by_cases heq : k - 1 = (toModel s).length
      · rw [if_pos (by omega), heq]
        simp
      · rw [if_neg (by omega)]
        have h1 : (1 : Nat) ≤ k - 1 - (toModel s).length := by omega
        rw [List.getElem?_eq_none (by simpa using h1),
            List.getElem?_eq_none (by omega)]

/-- Complete description of `get` after a truncation. -/
theorem get_truncFrom (s : σ) (i k : Nat) :
    get (truncFrom s i) k = if k < i then get s k else none := by
  rw [model_get, model_get, model_truncFrom]
  by_cases hk : k = 0
  · subst hk; simp
  · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk
    simp only [hk, if_false]
    by_cases hlt : k < i
    · rw [if_pos hlt]
      exact List.getElem?_take_of_lt (by omega)
    · rw [if_neg hlt]
      exact List.getElem?_eq_none (by simp; omega)

/-- Reading the tail slice agrees with reading the log directly. -/
theorem getElem?_sliceFrom (s : σ) (i n : Nat) (hi : 1 ≤ i) :
    (sliceFrom s i)[n]? = get s (i + n) := by
  rw [model_sliceFrom, model_get, if_neg (by omega)]
  rw [List.getElem?_drop]
  congr 1
  omega

/-- Two logs with the same model are indistinguishable through `get`. -/
theorem get_congr {s t : σ} (h : toModel s = toModel t) (i : Nat) :
    get s i = get t i := by
  rw [model_get, model_get, h]

end LogStore

end RaftKV
