import RaftKV.Storage.BTreeProof

/-!
# P4: what the tree contains, and why search finds it

The three properties in `BTreeProof.lean` are about where bytes go. This file is
about the tree being any good: a page image, read through a root cell, denotes a
list of bindings, and `lookup` returns exactly what that list says.

The invariant is the usual B-tree one, written as a mutual inductive:

* a **leaf** denotes its records, which are strictly increasing in key;
* a **branch** denotes the concatenation of its children's denotations, where the
  separators split the key space: everything left of `s` is `< s`, everything at
  or right of it is `≥ s`, and the separators themselves increase;
* every child of a branch sits at the same depth, so the tree is balanced.

Carrying the depth explicitly is what makes the fuel bound in `lookupAux`
respectable: a tree of depth `d` is searched correctly by any fuel above `d`.
-/

namespace RaftKV.BTree

/-- Strictly increasing in key. -/
def Sorted (m : List (Nat × ByteArray)) : Prop := m.Pairwise (fun a b => a.1 < b.1)

mutual

/-- `Denote pages lim d p m`: page `p` roots a depth-`d` subtree holding `m`. -/
inductive Denote (pages : Pages) (lim : Nat) : Nat → Nat → List (Nat × ByteArray) → Prop where
  | leaf {p : Nat} {recs : Array (Nat × ByteArray)} :
      p < lim → pages p = some (.leaf recs) → Sorted recs.toList →
      Denote pages lim 0 p recs.toList
  | branch {d p : Nat} {keys children : Array Nat} {m : List (Nat × ByteArray)} :
      p < lim → pages p = some (.branch keys children) →
      Chain pages lim d keys.toList children.toList m →
      Denote pages lim (d + 1) p m

/-- The children of one branch, with their separators. -/
inductive Chain (pages : Pages) (lim : Nat) :
    Nat → List Nat → List Nat → List (Nat × ByteArray) → Prop where
  | one {d c : Nat} {m : List (Nat × ByteArray)} :
      Denote pages lim d c m → Chain pages lim d [] [c] m
  | cons {d s : Nat} {ks : List Nat} {c : Nat} {cs : List Nat}
      {m ms : List (Nat × ByteArray)} :
      Denote pages lim d c m →
      (∀ kv ∈ m, kv.1 < s) →
      (∀ kv ∈ ms, s ≤ kv.1) →
      (∀ s' ∈ ks, s < s') →
      Chain pages lim d ks cs ms →
      Chain pages lim d (s :: ks) (c :: cs) (m ++ ms)

end

/-- What a list of bindings says about `k`. -/
def lookupList (m : List (Nat × ByteArray)) (k : Nat) : Option ByteArray :=
  (m.find? (fun r => r.1 == k)).map Prod.snd

/-- `childIndex` counts the separators at or below `k`. -/
theorem childIndex_eq (keys : Array Nat) (k : Nat) :
    childIndex keys k = (keys.toList.filter (fun s => s ≤ k)).length := rfl

end RaftKV.BTree

namespace RaftKV.BTree

/-! ## Search agrees with the contents -/

theorem get_of_lt {t : Tree} {pages : Pages} {lim p : Nat}
    (ht : t.next = lim) (h : p < lim) : t.get pages p = pages p := by
  unfold Tree.get; rw [if_pos (ht ▸ h)]

theorem find?_eq_none_of_ne {m : List (Nat × ByteArray)} {k : Nat}
    (h : ∀ kv ∈ m, kv.1 ≠ k) : m.find? (fun r => r.1 == k) = none := by
  rw [List.find?_eq_none]
  intro x hx
  simp only [beq_iff_eq]
  exact h x hx

theorem lookupList_append_left {m ms : List (Nat × ByteArray)} {k : Nat}
    (h : ∀ kv ∈ ms, kv.1 ≠ k) : lookupList (m ++ ms) k = lookupList m k := by
  unfold lookupList
  rw [List.find?_append]
  cases hm : m.find? (fun r => r.1 == k) with
  | some _ => rfl
  | none => rw [find?_eq_none_of_ne h]; rfl

theorem lookupList_append_right {m ms : List (Nat × ByteArray)} {k : Nat}
    (h : ∀ kv ∈ m, kv.1 ≠ k) : lookupList (m ++ ms) k = lookupList ms k := by
  unfold lookupList
  rw [List.find?_append, find?_eq_none_of_ne h]
  rfl

/-- Descending into the child `childIndex` picks out finds exactly what the branch holds. -/
theorem chain_lookup {pages : Pages} {lim d k fuel : Nat} {t : Tree} (ht : t.next = lim)
    (IH : ∀ p m, Denote pages lim d p m → lookupAux t pages k fuel p = lookupList m k)
    : ∀ {ks cs : List Nat} {m : List (Nat × ByteArray)}, Chain pages lim d ks cs m →
    (match cs[(ks.filter (fun s => s ≤ k)).length]? with
     | none => none
     | some c => lookupAux t pages k fuel c) = lookupList m k := by
  intro ks
  induction ks with
  | nil =>
      intro cs m hc
      cases hc with
      | one hd => exact IH _ _ hd
  | cons s ks ih =>
    intro cs m hc
    cases hc with
    | @cons _ _ _ c cs m1 ms hd hlt hge hks hrest =>
      by_cases hsk : s ≤ k
      · -- k is at or right of the separator: skip this child
        have hfil : (List.filter (fun s => decide (s ≤ k)) (s :: ks)).length
            = (List.filter (fun s => decide (s ≤ k)) ks).length + 1 := by
          simp [List.filter_cons, hsk, Nat.add_comm]
        rw [hfil]
        have : (c :: cs)[(List.filter (fun s => decide (s ≤ k)) ks).length + 1]?
            = cs[(List.filter (fun s => decide (s ≤ k)) ks).length]? := by
          simp [List.getElem?_cons_succ]
        rw [this, ih hrest]
        exact (lookupList_append_right (fun kv hkv =>
          Nat.ne_of_lt (Nat.lt_of_lt_of_le (hlt kv hkv) hsk))).symm
      · -- k is left of every separator: this child, and no other
        have hks' : List.filter (fun s => decide (s ≤ k)) ks = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx
          simp only [decide_eq_true_eq]
          exact Nat.not_le.mpr (Nat.lt_trans (Nat.not_le.mp hsk) (hks x hx))
        have hfil : (List.filter (fun s => decide (s ≤ k)) (s :: ks)).length = 0 := by
          simp [List.filter_cons, hsk, hks']
        rw [hfil]
        show lookupAux t pages k fuel c = _
        rw [IH _ _ hd]
        exact (lookupList_append_left (fun kv hkv =>
          fun he => absurd (he ▸ hge kv hkv) (Nat.not_le.mpr (Nat.not_le.mp hsk)))).symm

/-- **P4, for reads.** A tree of depth `d` is searched correctly by any fuel above `d`. -/
theorem denote_lookup {pages : Pages} {lim k : Nat} {t : Tree} (ht : t.next = lim) :
    ∀ (d : Nat) {p : Nat} {m : List (Nat × ByteArray)} {fuel : Nat},
      d < fuel → Denote pages lim d p m → lookupAux t pages k fuel p = lookupList m k := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro p m fuel hfuel hd
    cases fuel with
    | zero => exact absurd hfuel (by simp)
    | succ f =>
      cases hd with
      | @leaf p recs hp hpage _ =>
          rw [lookupAux, get_of_lt ht hp, hpage]
          rfl
      | @branch d' p keys children m hp hpage hchain =>
          rw [lookupAux, get_of_lt ht hp, hpage]
          dsimp only
          rw [childIndex_eq, ← Array.getElem?_toList]
          exact chain_lookup ht
            (fun q m' hq => ih d' (Nat.lt_succ_self _) (Nat.lt_of_succ_lt_succ hfuel) hq)
            hchain

end RaftKV.BTree

namespace RaftKV.BTree

/-! ## The scan, and that it comes out in order -/

theorem chain_toList {pages : Pages} {lim d fuel : Nat} {t : Tree} (ht : t.next = lim)
    (IH : ∀ p m, Denote pages lim d p m → toListAux t pages fuel p = m) :
    ∀ {ks cs : List Nat} {m : List (Nat × ByteArray)}, Chain pages lim d ks cs m →
      cs.flatMap (fun c => toListAux t pages fuel c) = m := by
  intro ks
  induction ks with
  | nil =>
      intro cs m hc
      cases hc with
      | one hd => rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]; exact IH _ _ hd
  | cons s ks ih =>
      intro cs m hc
      cases hc with
      | @cons _ _ _ c cs m1 ms hd _ _ _ hrest =>
          rw [List.flatMap_cons, IH _ _ hd, ih hrest]

/-- **P4, for scans.** The ordered scan of a depth-`d` tree is exactly its contents. -/
theorem denote_toList {pages : Pages} {lim : Nat} {t : Tree} (ht : t.next = lim) :
    ∀ (d : Nat) {p : Nat} {m : List (Nat × ByteArray)} {fuel : Nat},
      d < fuel → Denote pages lim d p m → toListAux t pages fuel p = m := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro p m fuel hfuel hd
    cases fuel with
    | zero => exact absurd hfuel (by simp)
    | succ f =>
      cases hd with
      | @leaf p recs hp hpage _ => rw [toListAux, get_of_lt ht hp, hpage]
      | @branch d' p keys children m hp hpage hchain =>
          rw [toListAux, get_of_lt ht hp, hpage]
          dsimp only
          exact chain_toList ht
            (fun q m' hq => ih d' (Nat.lt_succ_self _) (Nat.lt_of_succ_lt_succ hfuel) hq)
            hchain

/-! ## The contents are sorted -/

theorem sorted_append {m ms : List (Nat × ByteArray)}
    (h1 : Sorted m) (h2 : Sorted ms) (hlt : ∀ a ∈ m, ∀ b ∈ ms, a.1 < b.1) :
    Sorted (m ++ ms) := List.pairwise_append.mpr ⟨h1, h2, hlt⟩

theorem chain_sorted {pages : Pages} {lim d : Nat}
    (IH : ∀ p m, Denote pages lim d p m → Sorted m) :
    ∀ {ks cs : List Nat} {m : List (Nat × ByteArray)}, Chain pages lim d ks cs m → Sorted m := by
  intro ks
  induction ks with
  | nil => intro cs m hc; cases hc with | one hd => exact IH _ _ hd
  | cons s ks ih =>
      intro cs m hc
      cases hc with
      | @cons _ _ _ c cs m1 ms hd hlt hge _ hrest =>
          exact sorted_append (IH _ _ hd) (ih hrest)
            (fun a ha b hb => Nat.lt_of_lt_of_le (hlt a ha) (hge b hb))

/-- Everything a tree denotes is strictly increasing in key. -/
theorem denote_sorted {pages : Pages} {lim : Nat} :
    ∀ (d : Nat) {p : Nat} {m : List (Nat × ByteArray)}, Denote pages lim d p m → Sorted m := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro p m hd
    cases hd with
    | leaf _ _ hs => exact hs
    | @branch d' p keys children m _ _ hchain =>
        exact chain_sorted (fun q m' hq => ih d' (Nat.lt_succ_self _) hq) hchain

end RaftKV.BTree

namespace RaftKV.BTree

/--
A root cell is **well formed** over a page image when it denotes some contents at
a depth the search fuel can reach.
-/
def WF (t : Tree) (pages : Pages) (m : List (Nat × ByteArray)) : Prop :=
  match t.root with
  | none => m = []
  | some r => ∃ d, d < maxDepth ∧ Denote pages t.next d r m

/-- **P4 for reads, at the top.** `lookup` returns what the tree contains. -/
theorem lookup_correct {t : Tree} {pages : Pages} {m : List (Nat × ByteArray)} {k : Nat}
    (h : WF t pages m) : t.lookup pages k = lookupList m k := by
  unfold WF at h
  unfold Tree.lookup
  split at h
  · rename_i he; rw [he]; subst h; rfl
  · rename_i r he
    obtain ⟨d, hd, hden⟩ := h
    rw [he]
    exact denote_lookup rfl d hd hden

/-- **P4 for scans, at the top.** -/
theorem toList_correct {t : Tree} {pages : Pages} {m : List (Nat × ByteArray)}
    (h : WF t pages m) : t.toList pages = m := by
  unfold WF at h
  unfold Tree.toList
  split at h
  · rename_i he; rw [he]; exact h.symm
  · rename_i r he
    obtain ⟨d, hd, hden⟩ := h
    rw [he]
    exact denote_toList rfl d hd hden

/-- And what it returns is in key order. -/
theorem toList_sorted {t : Tree} {pages : Pages} {m : List (Nat × ByteArray)}
    (h : WF t pages m) : Sorted (t.toList pages) := by
  rw [toList_correct h]
  unfold WF at h
  split at h
  · subst h; exact List.Pairwise.nil
  · obtain ⟨d, _, hden⟩ := h; exact denote_sorted d hden

/-- The empty tree is well formed and holds nothing. -/
theorem wf_empty (pages : Pages) : WF Tree.empty pages [] := rfl

end RaftKV.BTree
