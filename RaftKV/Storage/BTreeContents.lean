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

/-- A lower bound, absent at the left edge of the tree. -/
def Lo : Option Nat → Nat → Prop
  | none, _ => True
  | some l, k => l ≤ k

/-- An upper bound, absent at the right edge. -/
def Hi : Option Nat → Nat → Prop
  | none, _ => True
  | some h, k => k < h

/-- The half-open range a subtree is responsible for. -/
def InRange (lo hi : Option Nat) (k : Nat) : Prop := Lo lo k ∧ Hi hi k

theorem Lo.mono {lo : Option Nat} {s s' : Nat} (h : Lo lo s) (hs : s ≤ s') : Lo lo s' := by
  cases lo with
  | none => trivial
  | some l => exact Nat.le_trans h hs

theorem Hi.mono {hi : Option Nat} {s s' : Nat} (h : Hi hi s) (hs : s' ≤ s) : Hi hi s' := by
  cases hi with
  | none => trivial
  | some r => exact Nat.lt_of_le_of_lt hs h

mutual

/--
`Denote pages lim d lo hi p m`: page `p` roots a depth-`d` subtree responsible
for the key range `[lo, hi)` and holding exactly `m`.

The range is the part that makes splits work. Contents alone are not enough: a
node can be split at a separator that lies in its range but between none of its
records, and only the range says where that separator may go in the parent.
-/
inductive Denote (pages : Pages) (lim : Nat) :
    Nat → Option Nat → Option Nat → Nat → List (Nat × ByteArray) → Prop where
  | leaf {p : Nat} {recs : Array (Nat × ByteArray)} {lo hi : Option Nat} :
      p < lim → pages p = some (.leaf recs) → Sorted recs.toList →
      (∀ kv ∈ recs.toList, InRange lo hi kv.1) →
      Denote pages lim 0 lo hi p recs.toList
  | branch {d p : Nat} {keys children : Array Nat} {lo hi : Option Nat}
      {m : List (Nat × ByteArray)} :
      p < lim → pages p = some (.branch keys children) →
      Chain pages lim d lo hi keys.toList children.toList m →
      Denote pages lim (d + 1) lo hi p m

/-- The children of one branch, each with the range its separators carve out. -/
inductive Chain (pages : Pages) (lim : Nat) :
    Nat → Option Nat → Option Nat → List Nat → List Nat → List (Nat × ByteArray) → Prop where
  | one {d c : Nat} {lo hi : Option Nat} {m : List (Nat × ByteArray)} :
      Denote pages lim d lo hi c m → Chain pages lim d lo hi [] [c] m
  | cons {d s c : Nat} {lo hi : Option Nat} {ks cs : List Nat}
      {m ms : List (Nat × ByteArray)} :
      Denote pages lim d lo (some s) c m →
      InRange lo hi s →
      Chain pages lim d (some s) hi ks cs ms →
      Chain pages lim d lo hi (s :: ks) (c :: cs) (m ++ ms)

end

/-- What a list of bindings says about `k`. -/
def lookupList (m : List (Nat × ByteArray)) (k : Nat) : Option ByteArray :=
  (m.find? (fun r => r.1 == k)).map Prod.snd

/-- `childIndex` counts the separators at or below `k`. -/
theorem childIndex_eq (keys : Array Nat) (k : Nat) :
    childIndex keys k = (keys.toList.filter (fun s => s ≤ k)).length := rfl

/-! ## Everything a subtree holds is inside its range -/

theorem chain_range {pages : Pages} {lim d : Nat}
    (IH : ∀ lo hi p m, Denote pages lim d lo hi p m → ∀ kv ∈ m, InRange lo hi kv.1) :
    ∀ {lo hi : Option Nat} {ks cs : List Nat} {m : List (Nat × ByteArray)},
      Chain pages lim d lo hi ks cs m → ∀ kv ∈ m, InRange lo hi kv.1 := by
  intro lo hi ks
  induction ks generalizing lo with
  | nil =>
      intro cs m hc
      cases hc with
      | one hd => exact IH _ _ _ _ hd
  | cons s ks ih =>
      intro cs m hc
      cases hc with
      | @cons _ _ _ _ _ _ cs m1 ms hd hs hrest =>
          intro kv hkv
          rcases List.mem_append.mp hkv with h | h
          · exact ⟨(IH _ _ _ _ hd kv h).1, Hi.mono hs.2 (Nat.le_of_lt (IH _ _ _ _ hd kv h).2)⟩
          · exact ⟨Lo.mono hs.1 (ih hrest kv h).1, (ih hrest kv h).2⟩

/-- Every key a subtree holds lies in the range it is responsible for. -/
theorem denote_range {pages : Pages} {lim : Nat} :
    ∀ (d : Nat) {lo hi : Option Nat} {p : Nat} {m : List (Nat × ByteArray)},
      Denote pages lim d lo hi p m → ∀ kv ∈ m, InRange lo hi kv.1 := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro lo hi p m hd
    cases hd with
    | leaf _ _ _ hr => exact hr
    | @branch d' p keys children lo hi m _ _ hchain =>
        exact chain_range (fun lo hi q m' hq => ih d' (Nat.lt_succ_self _) hq) hchain

/-- Separators are themselves inside the range of the branch that holds them. -/
theorem chain_keys {pages : Pages} {lim d : Nat} :
    ∀ {lo hi : Option Nat} {ks cs : List Nat} {m : List (Nat × ByteArray)},
      Chain pages lim d lo hi ks cs m → ∀ s' ∈ ks, InRange lo hi s' := by
  intro lo hi ks
  induction ks generalizing lo with
  | nil => intro cs m hc s' hs'; exact absurd hs' (by simp)
  | cons s ks ih =>
      intro cs m hc
      cases hc with
      | @cons _ _ _ _ _ _ cs m1 ms hd hs hrest =>
          intro s' hs'
          rcases List.mem_cons.mp hs' with h | h
          · exact h ▸ hs
          · exact ⟨Lo.mono hs.1 (ih hrest s' h).1, (ih hrest s' h).2⟩

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

/-- `childIndex` picks the one child whose range can contain `k`. -/
theorem chain_lookup {pages : Pages} {lim d k fuel : Nat} {t : Tree} (ht : t.next = lim)
    (IH : ∀ lo hi p m, Denote pages lim d lo hi p m →
      lookupAux t pages k fuel p = lookupList m k) :
    ∀ {lo hi : Option Nat} {ks cs : List Nat} {m : List (Nat × ByteArray)},
      Chain pages lim d lo hi ks cs m →
      (match cs[(ks.filter (fun s => s ≤ k)).length]? with
       | none => none
       | some c => lookupAux t pages k fuel c) = lookupList m k := by
  intro lo hi ks
  induction ks generalizing lo with
  | nil =>
      intro cs m hc
      cases hc with
      | one hd => exact IH _ _ _ _ hd
  | cons s ks ih =>
    intro cs m hc
    cases hc with
    | @cons _ _ c _ _ _ cs m1 ms hd hs hrest =>
      by_cases hsk : s ≤ k
      · -- at or right of the separator: this child's range excludes `k`
        have hfil : (List.filter (fun s => decide (s ≤ k)) (s :: ks)).length
            = (List.filter (fun s => decide (s ≤ k)) ks).length + 1 := by
          simp [hsk, Nat.add_comm]
        rw [hfil]
        have hidx : (c :: cs)[(List.filter (fun s => decide (s ≤ k)) ks).length + 1]?
            = cs[(List.filter (fun s => decide (s ≤ k)) ks).length]? := by
          simp [List.getElem?_cons_succ]
        rw [hidx, ih hrest]
        exact (lookupList_append_right (fun kv hkv =>
          Nat.ne_of_lt (Nat.lt_of_lt_of_le (denote_range _ hd kv hkv).2 hsk))).symm
      · -- left of every separator from here on
        have hks' : List.filter (fun s => decide (s ≤ k)) ks = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx
          simp only [decide_eq_true_eq]
          exact Nat.not_le.mpr (Nat.lt_of_lt_of_le (Nat.not_le.mp hsk) (chain_keys hrest x hx).1)
        have hfil : (List.filter (fun s => decide (s ≤ k)) (s :: ks)).length = 0 := by
          simp [hsk, hks']
        rw [hfil]
        show lookupAux t pages k fuel c = _
        rw [IH _ _ _ _ hd]
        refine (lookupList_append_left (fun kv hkv he => ?_)).symm
        exact absurd (he ▸ (chain_range (fun lo hi q m' hq => denote_range _ hq) hrest kv hkv).1)
          (Nat.not_le.mpr (Nat.not_le.mp hsk))

/-- **P4, for reads.** A tree of depth `d` is searched correctly by any fuel above `d`. -/
theorem denote_lookup {pages : Pages} {lim k : Nat} {t : Tree} (ht : t.next = lim) :
    ∀ (d : Nat) {lo hi : Option Nat} {p : Nat} {m : List (Nat × ByteArray)} {fuel : Nat},
      d < fuel → Denote pages lim d lo hi p m → lookupAux t pages k fuel p = lookupList m k := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro lo hi p m fuel hfuel hd
    cases fuel with
    | zero => exact absurd hfuel (by simp)
    | succ f =>
      cases hd with
      | @leaf p recs _ _ hp hpage _ _ => rw [lookupAux, get_of_lt ht hp, hpage]; rfl
      | @branch d' p keys children lo hi m hp hpage hchain =>
          rw [lookupAux, get_of_lt ht hp, hpage]
          dsimp only
          rw [childIndex_eq, ← Array.getElem?_toList]
          exact chain_lookup ht
            (fun _ _ q m' hq => ih d' (Nat.lt_succ_self _) (Nat.lt_of_succ_lt_succ hfuel) hq)
            hchain

/-! ## The scan, and that it comes out in order -/

theorem chain_toList {pages : Pages} {lim d fuel : Nat} {t : Tree}
    (IH : ∀ lo hi p m, Denote pages lim d lo hi p m → toListAux t pages fuel p = m) :
    ∀ {lo hi : Option Nat} {ks cs : List Nat} {m : List (Nat × ByteArray)},
      Chain pages lim d lo hi ks cs m →
      cs.flatMap (fun c => toListAux t pages fuel c) = m := by
  intro lo hi ks
  induction ks generalizing lo with
  | nil =>
      intro cs m hc
      cases hc with
      | one hd => rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]; exact IH _ _ _ _ hd
  | cons s ks ih =>
      intro cs m hc
      cases hc with
      | @cons _ _ _ _ _ _ cs m1 ms hd _ hrest =>
          rw [List.flatMap_cons, IH _ _ _ _ hd, ih hrest]

/-- **P4, for scans.** The ordered scan of a depth-`d` tree is exactly its contents. -/
theorem denote_toList {pages : Pages} {lim : Nat} {t : Tree} (ht : t.next = lim) :
    ∀ (d : Nat) {lo hi : Option Nat} {p : Nat} {m : List (Nat × ByteArray)} {fuel : Nat},
      d < fuel → Denote pages lim d lo hi p m → toListAux t pages fuel p = m := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro lo hi p m fuel hfuel hd
    cases fuel with
    | zero => exact absurd hfuel (by simp)
    | succ f =>
      cases hd with
      | @leaf p recs _ _ hp hpage _ _ => rw [toListAux, get_of_lt ht hp, hpage]
      | @branch d' p keys children lo hi m hp hpage hchain =>
          rw [toListAux, get_of_lt ht hp, hpage]
          dsimp only
          exact chain_toList
            (fun _ _ q m' hq => ih d' (Nat.lt_succ_self _) (Nat.lt_of_succ_lt_succ hfuel) hq)
            hchain

/-! ## The contents are sorted -/

theorem sorted_append {m ms : List (Nat × ByteArray)}
    (h1 : Sorted m) (h2 : Sorted ms) (hlt : ∀ a ∈ m, ∀ b ∈ ms, a.1 < b.1) :
    Sorted (m ++ ms) := List.pairwise_append.mpr ⟨h1, h2, hlt⟩

theorem chain_sorted {pages : Pages} {lim d : Nat}
    (IH : ∀ lo hi p m, Denote pages lim d lo hi p m → Sorted m) :
    ∀ {lo hi : Option Nat} {ks cs : List Nat} {m : List (Nat × ByteArray)},
      Chain pages lim d lo hi ks cs m → Sorted m := by
  intro lo hi ks
  induction ks generalizing lo with
  | nil => intro cs m hc; cases hc with | one hd => exact IH _ _ _ _ hd
  | cons s ks ih =>
      intro cs m hc
      cases hc with
      | @cons _ _ _ _ _ _ cs m1 ms hd _ hrest =>
          refine sorted_append (IH _ _ _ _ hd) (ih hrest) (fun a ha b hb => ?_)
          exact Nat.lt_of_lt_of_le (denote_range _ hd a ha).2
            (chain_range (fun lo hi q m' hq => denote_range _ hq) hrest b hb).1

/-- Everything a tree denotes is strictly increasing in key. -/
theorem denote_sorted {pages : Pages} {lim : Nat} :
    ∀ (d : Nat) {lo hi : Option Nat} {p : Nat} {m : List (Nat × ByteArray)},
      Denote pages lim d lo hi p m → Sorted m := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro lo hi p m hd
    cases hd with
    | leaf _ _ hs _ => exact hs
    | @branch d' p keys children lo hi m _ _ hchain =>
        exact chain_sorted (fun _ _ q m' hq => ih d' (Nat.lt_succ_self _) hq) hchain

/-! ## At the top -/

/-- A root cell is **well formed** when it denotes contents at a reachable depth. -/
def WF (t : Tree) (pages : Pages) (m : List (Nat × ByteArray)) : Prop :=
  match t.root with
  | none => m = []
  | some r => ∃ d, d < maxDepth ∧ Denote pages t.next d none none r m

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
