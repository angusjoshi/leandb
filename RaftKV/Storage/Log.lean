import RaftKV.Core.Types

/-!
# The replicated log, abstractly

This is the project's flagship abstraction and sets the pattern every other
swappable component follows.

`LogStore` carries **operations only** and is computable. `LawfulLogStore`
carries the refinement mapping `toModel` together with laws saying each
operation commutes with it.

The split matters for more than tidiness. A segmented or B-tree-backed log
cannot *compute* its full contents without paging the whole log into memory.
Because `toModel` lives in the lawful class, such an instance may be
`noncomputable` while the operational instance stays fully executable. Proofs
mention `toModel`; compiled code cannot.

Note also what is *absent*: there is no `toList` operation. Materialising the
whole log is a proof-level fiction, never something the running system does.
Reads are `get` (one entry) and `sliceFrom` (a bounded suffix), both of which a
segmented log implements cheaply.

Indices are 1-based: `get s 0 = none` always.

## Compaction

A log that only grows is not a log you can run for a year. `compact s i`
discards every entry strictly below `i`, and `firstIndex` says how far the
discarding has gone. The entry at `firstIndex` itself is **kept**: it is the
anchor the `AppendEntries` consistency check needs, so no separate
"last included term" field has to be threaded through the protocol and its
proofs.

The model is a `List (Option Entry)` rather than a `List Entry`, with `none` at
a discarded position. That choice is what makes compaction cheap to prove
around: `get` already returned `Option Entry`, so *every* protocol proof phrased
over `get` — which is all of them — keeps working verbatim. Only the laws in
this file and the instances below know that a hole is a hole.
-/

namespace RaftKV

/-- Executable operations of a Raft log. -/
class LogStore (σ : Type) where
  /-- The empty log. -/
  empty : σ
  /-- Append one entry at the end, giving it index `size + 1`. -/
  append : σ → Entry → σ
  /-- Fetch the entry at a 1-based index, or `none` if out of range or discarded. -/
  get : σ → Nat → Option Entry
  /-- Delete every entry at index `≥ i`, keeping the prefix of length `i - 1`. -/
  truncFrom : σ → Nat → σ
  /-- Highest index the log reaches, discarded entries included. -/
  size : σ → Nat
  /-- Every entry at index `≥ i`, in order. Bounded: used to fill `AppendEntries`. -/
  sliceFrom : σ → Nat → List Entry
  /-- Lowest index that may still be present. `1` until something is discarded. -/
  firstIndex : σ → Nat
  /-- Discard every entry strictly below `i`. The entry at `i` is kept as the anchor. -/
  compact : σ → Nat → σ

/--
The refinement mapping from a log implementation to its mathematical model,
plus the laws that make it a refinement.

Proving these laws is the *entire* cost of swapping in a new log
implementation. Every theorem in `RaftKV.Proof` is stated over `LogStore.get`
and so transports to any lawful instance unchanged.
-/
class LawfulLogStore (σ : Type) [LogStore σ] where
  /-- The abstract contents: `none` at a discarded index. Proof-level only. -/
  toModel : σ → List (Option Entry)
  model_empty : toModel (LogStore.empty : σ) = []
  model_append : ∀ (s : σ) (e : Entry),
    toModel (LogStore.append s e) = toModel s ++ [some e]
  model_get : ∀ (s : σ) (i : Nat),
    LogStore.get s i = if i = 0 then none else ((toModel s)[i - 1]?).join
  model_truncFrom : ∀ (s : σ) (i : Nat),
    toModel (LogStore.truncFrom s i) = (toModel s).take (i - 1)
  model_size : ∀ (s : σ), LogStore.size s = (toModel s).length
  /-- Reading a suffix is exact, provided it starts at or above the first live index. -/
  model_sliceFrom : ∀ (s : σ) (i : Nat), LogStore.firstIndex s ≤ i →
    (LogStore.sliceFrom s i).map some = (toModel s).drop (i - 1)
  /--
  Compaction replaces the entries below `i` with holes and touches nothing else.

  Stated for a well-formed call — compacting to an index that is present. The
  protocol only ever compacts up to `lastApplied`, which is inside the window.
  -/
  model_compact : ∀ (s : σ) (i : Nat),
    LogStore.firstIndex s ≤ i → i ≤ LogStore.size s →
    toModel (LogStore.compact s i)
      = List.replicate (i - 1) none ++ (toModel s).drop (i - 1)
  /-- The live window starts at 1 or later. -/
  first_pos : ∀ (s : σ), 1 ≤ LogStore.firstIndex s
  /-- Below the window there is nothing: this is what a hole means. -/
  get_lt_first : ∀ (s : σ) (k : Nat), k < LogStore.firstIndex s → LogStore.get s k = none
  /-- Inside the window there are no holes: the discarded indices are exactly a prefix. -/
  get_isSome : ∀ (s : σ) (k : Nat), LogStore.firstIndex s ≤ k → k ≤ LogStore.size s →
    (LogStore.get s k).isSome
  /-- A fresh log has discarded nothing. -/
  first_empty : LogStore.firstIndex (LogStore.empty : σ) = 1
  /-- Appending discards nothing. -/
  first_append : ∀ (s : σ) (e : Entry),
    LogStore.firstIndex (LogStore.append s e) = LogStore.firstIndex s
  /-- Truncating the tail discards nothing at the head. -/
  first_truncFrom : ∀ (s : σ) (i : Nat),
    LogStore.firstIndex (LogStore.truncFrom s i) = max 1 (min (LogStore.firstIndex s) i)
  /-- Compaction moves the window forward to the point compacted to. -/
  first_compact : ∀ (s : σ) (i : Nat),
    LogStore.firstIndex s ≤ i → i ≤ LogStore.size s →
    LogStore.firstIndex (LogStore.compact s i) = i

export LawfulLogStore (toModel model_empty model_append model_get model_truncFrom
  model_size model_sliceFrom model_compact first_pos get_lt_first get_isSome
  first_empty first_append first_truncFrom first_compact)

attribute [simp] model_empty model_append model_size first_empty first_append

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

/-- Is index `i` still readable? -/
def live (s : σ) (i : Nat) : Bool := firstIndex s ≤ i && i ≤ lastIndex s

/--
The lowest index a leader may start an `AppendEntries` payload at.

`AppendEntries` names the entry *below* the payload, so the sender must be able
to state that entry's term. Index `0` is the virtual anchor of an uncompacted
log and has term `0` by convention; otherwise the anchor must be an entry the
sender still holds, so the payload starts one past the window's first index.

For a log that has never been compacted this is `1`, exactly as before.
-/
def sendFloor (s : σ) : Nat := if firstIndex s = 1 then 1 else firstIndex s + 1

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

/-- An entry that reads back is inside the live window. -/
theorem le_lastIndex_of_get {s : σ} {i : Nat} {e : Entry} (h : get s i = some e) :
    i ≤ lastIndex s := by
  rw [model_get] at h
  by_cases hi : i = 0
  · rw [if_pos hi] at h; exact absurd h (by simp)
  · rw [if_neg hi] at h
    simp only [lastIndex, model_size]
    rcases Nat.lt_or_ge (i - 1) (toModel s).length with hlt | hge
    · omega
    · rw [List.getElem?_eq_none hge] at h
      exact absurd h (by simp)

theorem firstIndex_le_of_get {s : σ} {i : Nat} {e : Entry} (h : get s i = some e) :
    firstIndex s ≤ i := by
  rcases Nat.lt_or_ge i (firstIndex s) with hlt | hge
  · rw [get_lt_first s i hlt] at h; exact absurd h (by simp)
  · exact hge

theorem firstIndex_le_of_termAt {s : σ} {i t : Nat} (h : termAt s i = some t) :
    firstIndex s ≤ i := by
  unfold termAt at h
  cases hg : get s i with
  | none => rw [hg] at h; exact absurd h (by simp)
  | some e => exact firstIndex_le_of_get hg

/-- An index is readable exactly when it is inside the live window. -/
theorem get_isSome_iff (s : σ) (i : Nat) :
    (get s i).isSome ↔ firstIndex s ≤ i ∧ i ≤ lastIndex s := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp h
    exact ⟨firstIndex_le_of_get he, le_lastIndex_of_get he⟩
  · exact fun h => get_isSome s i h.1 h.2

/-- Appending never disturbs an entry that already existed. -/
theorem get_append_of_le (s : σ) (e : Entry) (i : Nat) (h : i ≤ lastIndex s) :
    get (append s e) i = get s i := by
  rw [model_get, model_get, model_append]
  by_cases hi : i = 0
  · simp [hi]
  · simp only [lastIndex, model_size] at h
    simp only [hi, if_false]
    rw [List.getElem?_append_left (by omega)]

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
  · simp only [hj, if_false]
    rw [List.getElem?_take_of_lt (by omega)]

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
  · have hlen : lastIndex s = (toModel s).length := by simp [lastIndex, model_size]
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
  · simp only [hk, if_false]
    by_cases hlt : k < i
    · rw [if_pos hlt, List.getElem?_take_of_lt (by omega)]
    · rw [if_neg hlt, List.getElem?_eq_none (by simp; omega)]
      rfl

/-- Reading the tail slice agrees with reading the log directly. -/
theorem getElem?_sliceFrom (s : σ) (i n : Nat) (hi : firstIndex s ≤ i) :
    (sliceFrom s i)[n]? = get s (i + n) := by
  have h1 : 1 ≤ i := Nat.le_trans (first_pos s) hi
  have hm := congrArg (fun l => l[n]?) (model_sliceFrom s i hi)
  simp only [List.getElem?_map, List.getElem?_drop] at hm
  have harg : i - 1 + n = i + n - 1 := by omega
  rw [harg] at hm
  rw [model_get, if_neg (by omega), ← hm]
  cases (sliceFrom s i)[n]? <;> rfl

/-- Two logs with the same model are indistinguishable through `get`. -/
theorem get_congr {s t : σ} (h : toModel s = toModel t) (i : Nat) :
    get s i = get t i := by
  rw [model_get, model_get, h]

/-- Truncating the tail can only move the window's start down, never up. -/
theorem firstIndex_truncFrom_le (s : σ) (i : Nat) :
    firstIndex (truncFrom s i) ≤ firstIndex s := by
  rw [first_truncFrom]
  have := first_pos s
  omega

/-- The splice recursion's window bound, for the branch that appends. -/
theorem first_le_succ_append {s : σ} {i : Nat} (e : Entry) (h : firstIndex s ≤ i) :
    firstIndex (append s e) ≤ i + 1 := by
  rw [first_append]; omega

/-- The splice recursion's window bound, for the branch that truncates first. -/
theorem first_le_succ_trunc {s : σ} {i : Nat} (e : Entry) (h : firstIndex s ≤ i) :
    firstIndex (append (truncFrom s i) e) ≤ i + 1 := by
  rw [first_append]
  exact Nat.le_trans (firstIndex_truncFrom_le s i) (by omega)

/-- A payload index at or above the send floor sits strictly inside the window. -/
theorem first_lt_of_sendFloor {s : σ} {k : Nat} (h1 : sendFloor s ≤ k) (h2 : 2 ≤ k) :
    firstIndex s < k := by
  unfold sendFloor at h1
  split at h1
  · omega
  · omega

/-- The send floor is inside the window. -/
theorem firstIndex_le_sendFloor (s : σ) : firstIndex s ≤ sendFloor s := by
  unfold sendFloor
  have := first_pos s
  split <;> omega

/-- The send floor is at least one. -/
theorem one_le_sendFloor (s : σ) : 1 ≤ sendFloor s := by
  unfold sendFloor; split <;> omega

/-! ### Compaction -/

/-- Compaction changes no index's contents, it only makes low ones unreadable. -/
theorem get_compact (s : σ) (i k : Nat) (h1 : firstIndex s ≤ i) (h2 : i ≤ lastIndex s) :
    get (compact s i) k = if k < i then none else get s k := by
  have hi1 : 1 ≤ i := Nat.le_trans (first_pos s) h1
  have hlen : i - 1 ≤ (toModel s).length := by
    simp only [lastIndex, model_size] at h2; omega
  rw [model_get, model_get, model_compact s i h1 h2]
  by_cases hk : k = 0
  · subst hk; simp
  · simp only [hk, if_false]
    have hrep : (List.replicate (i - 1) (none : Option Entry)).length = i - 1 :=
      List.length_replicate ..
    have hdrop : ((toModel s).drop (i - 1)).length = (toModel s).length - (i - 1) :=
      List.length_drop ..
    by_cases hlt : k < i
    · rw [if_pos hlt, List.getElem?_append_left (by omega), List.getElem?_replicate,
        if_pos (by omega)]
      rfl
    · rw [if_neg hlt, List.getElem?_append_right (by omega), List.getElem?_drop]
      congr 2
      omega

/-- Compaction preserves the log's extent. -/
theorem lastIndex_compact (s : σ) (i : Nat) (h1 : firstIndex s ≤ i) (h2 : i ≤ lastIndex s) :
    lastIndex (compact s i) = lastIndex s := by
  have hlen : i - 1 ≤ (toModel s).length := by
    simp only [lastIndex, model_size] at h2; omega
  simp only [lastIndex, model_size] at h2 ⊢
  rw [model_compact s i h1 (by simpa [lastIndex, model_size] using h2)]
  simp only [List.length_append, List.length_replicate, List.length_drop]
  omega

/-- Entries at or above the compaction point survive. -/
theorem get_compact_of_le (s : σ) (i k : Nat) (h1 : firstIndex s ≤ i) (h2 : i ≤ lastIndex s)
    (h : i ≤ k) : get (compact s i) k = get s k := by
  rw [get_compact s i k h1 h2, if_neg (by omega)]

/-- And the window starts exactly where we compacted to. -/
theorem firstIndex_compact (s : σ) (i : Nat) (h1 : firstIndex s ≤ i) (h2 : i ≤ lastIndex s) :
    firstIndex (compact s i) = i := first_compact s i h1 h2

end LogStore

end RaftKV
