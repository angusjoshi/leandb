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

/-- The tail of a sorted list is sorted. -/
theorem sorted_tail {r : Nat × ByteArray} {rs : List (Nat × ByteArray)}
    (h : Sorted (r :: rs)) : Sorted rs := (List.pairwise_cons.mp h).2

/-- The head of a sorted list is below every other key. -/
theorem sorted_head {r : Nat × ByteArray} {rs : List (Nat × ByteArray)}
    (h : Sorted (r :: rs)) : ∀ q ∈ rs, r.1 < q.1 := (List.pairwise_cons.mp h).1

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

/-- The weaker upper bound a *separator* satisfies: it may sit at the top of the range. -/
def HiLe : Option Nat → Nat → Prop
  | none, _ => True
  | some h, k => k ≤ h

/--
Where a separator may sit: at or above the low end, at or below the high end.

Non-strict at the top on purpose. A split promotes a key from inside a child, and
that key can equal the separator above it; demanding strict inequality would make
the split of a branch fail to typecheck as a branch. The cost is that a child's
range may be empty, which simply means it holds nothing.
-/
def SepIn (lo hi : Option Nat) (k : Nat) : Prop := Lo lo k ∧ HiLe hi k

theorem Lo.mono {lo : Option Nat} {s s' : Nat} (h : Lo lo s) (hs : s ≤ s') : Lo lo s' := by
  cases lo with
  | none => trivial
  | some l => exact Nat.le_trans h hs

theorem Hi.mono {hi : Option Nat} {s s' : Nat} (h : Hi hi s) (hs : s' ≤ s) : Hi hi s' := by
  cases hi with
  | none => trivial
  | some r => exact Nat.lt_of_le_of_lt hs h

theorem Hi.of_sep {hi : Option Nat} {s k : Nat} (h : HiLe hi s) (hk : k < s) : Hi hi k := by
  cases hi with
  | none => trivial
  | some r => exact Nat.lt_of_lt_of_le hk h

theorem HiLe.of_hi {hi : Option Nat} {k : Nat} (h : Hi hi k) : HiLe hi k := by
  cases hi with
  | none => trivial
  | some r => exact Nat.le_of_lt h

theorem HiLe.mono {hi : Option Nat} {s s' : Nat} (h : HiLe hi s) (hs : s' ≤ s) : HiLe hi s' := by
  cases hi with
  | none => trivial
  | some r => exact Nat.le_trans hs h

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
      SepIn lo hi s →
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
          · exact ⟨(IH _ _ _ _ hd kv h).1, Hi.of_sep hs.2 (IH _ _ _ _ hd kv h).2⟩
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
      Chain pages lim d lo hi ks cs m → ∀ s' ∈ ks, SepIn lo hi s' := by
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

/-- A root cell denoting `m` at depth `d`. -/
def WFd (t : Tree) (pages : Pages) (d : Nat) (m : List (Nat × ByteArray)) : Prop :=
  match t.root with
  | none => m = []
  | some r => Denote pages t.next d none none r m

/--
A root cell is **well formed** when it denotes contents at a depth the search
fuel can reach. Depth is bounded by `maxDepth`, and an insert can add one level,
so the statements below say what happens to the depth rather than assuming it
stays put.
-/
def WF (t : Tree) (pages : Pages) (m : List (Nat × ByteArray)) : Prop :=
  ∃ d, d < maxDepth ∧ WFd t pages d m

/-- **P4 for reads, at the top.** `lookup` returns what the tree contains. -/
theorem lookup_correct {t : Tree} {pages : Pages} {m : List (Nat × ByteArray)} {k : Nat}
    (h : WF t pages m) : t.lookup pages k = lookupList m k := by
  obtain ⟨d, hd, hden⟩ := h
  unfold WFd at hden
  unfold Tree.lookup
  split at hden
  · rename_i he; rw [he]; subst hden; rfl
  · rename_i r he
    rw [he]
    exact denote_lookup rfl d hd hden

/-- **P4 for scans, at the top.** -/
theorem toList_correct {t : Tree} {pages : Pages} {m : List (Nat × ByteArray)}
    (h : WF t pages m) : t.toList pages = m := by
  obtain ⟨d, hd, hden⟩ := h
  unfold WFd at hden
  unfold Tree.toList
  split at hden
  · rename_i he; rw [he]; exact hden.symm
  · rename_i r he
    rw [he]
    exact denote_toList rfl d hd hden

/-- And what it returns is in key order. -/
theorem toList_sorted {t : Tree} {pages : Pages} {m : List (Nat × ByteArray)}
    (h : WF t pages m) : Sorted (t.toList pages) := by
  rw [toList_correct h]
  obtain ⟨d, _, hden⟩ := h
  unfold WFd at hden
  split at hden
  · subst hden; exact List.Pairwise.nil
  · exact denote_sorted d hden

/-- The empty tree is well formed and holds nothing. -/
theorem wf_empty (pages : Pages) : WF Tree.empty pages [] := ⟨0, by decide, rfl⟩

end RaftKV.BTree

namespace RaftKV.BTree

/-!
## Framing: an old subtree keeps its meaning after a commit

This is P3 again, at the level of the invariant rather than of a single read.
A commit writes only at or above the old high-water mark, so every page an
existing subtree reaches still holds what it held, and the subtree still denotes
what it denoted — now under the larger mark, which is what lets the new root
cell reuse the parts of the tree the update did not touch.
-/

theorem chain_frame {pages pages' : Pages} {lim lim' d : Nat}
    (IH : ∀ lo hi p m, Denote pages lim d lo hi p m → Denote pages' lim' d lo hi p m) :
    ∀ {lo hi : Option Nat} {ks cs : List Nat} {m : List (Nat × ByteArray)},
      Chain pages lim d lo hi ks cs m → Chain pages' lim' d lo hi ks cs m := by
  intro lo hi ks
  induction ks generalizing lo with
  | nil => intro cs m hc; cases hc with | one hd => exact .one (IH _ _ _ _ hd)
  | cons s ks ih =>
      intro cs m hc
      cases hc with
      | @cons _ _ c _ _ _ cs m1 ms hd hs hrest => exact .cons (IH _ _ _ _ hd) hs (ih hrest)

/-- An existing subtree denotes the same contents under any image that agrees below `lim`. -/
theorem denote_frame {pages pages' : Pages} {lim lim' : Nat}
    (hf : ∀ q, q < lim → pages' q = pages q) (hl : lim ≤ lim') :
    ∀ (d : Nat) {lo hi : Option Nat} {p : Nat} {m : List (Nat × ByteArray)},
      Denote pages lim d lo hi p m → Denote pages' lim' d lo hi p m := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro lo hi p m hd
    cases hd with
    | leaf hp hpage hs hr =>
        exact .leaf (Nat.lt_of_lt_of_le hp hl) (by rw [hf _ hp]; exact hpage) hs hr
    | @branch d' p keys children lo hi m hp hpage hchain =>
        refine .branch (Nat.lt_of_lt_of_le hp hl) (by rw [hf _ hp]; exact hpage) ?_
        exact chain_frame (fun _ _ q m' hq => ih d' (Nat.lt_succ_self _) hq) hchain

end RaftKV.BTree

namespace RaftKV.BTree

/-! ## What inserting into a sorted list does -/

theorem insertRec_mem {m : List (Nat × ByteArray)} {k : Nat} {v : ByteArray}
    {kv : Nat × ByteArray} : kv ∈ insertRec m k v → kv ∈ m ∨ kv = (k, v) := by
  induction m with
  | nil => intro h; simp only [insertRec, List.mem_singleton] at h; exact Or.inr h
  | cons a m ih =>
      intro h
      rw [insertRec] at h
      split at h
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inr h
        · exact Or.inl (List.mem_cons_of_mem _ h)
      · split at h
        · rcases List.mem_cons.mp h with h | h
          · exact Or.inr h
          · exact Or.inl h
        · rcases List.mem_cons.mp h with h | h
          · exact Or.inl (h ▸ List.mem_cons_self ..)
          · rcases ih h with h' | h'
            · exact Or.inl (List.mem_cons_of_mem _ h')
            · exact Or.inr h'

theorem insertRec_sorted {m : List (Nat × ByteArray)} {k : Nat} {v : ByteArray}
    (h : Sorted m) : Sorted (insertRec m k v) := by
  induction m with
  | nil => exact List.pairwise_singleton ..
  | cons a m ih =>
      obtain ⟨ha, hm⟩ := List.pairwise_cons.mp h
      rw [insertRec]
      split
      · rename_i he
        have : k = a.1 := by simpa using he
        refine List.pairwise_cons.mpr ⟨?_, hm⟩
        intro b hb; exact this ▸ ha b hb
      · split
        · rename_i hlt
          refine List.pairwise_cons.mpr ⟨?_, h⟩
          intro b hb
          rcases List.mem_cons.mp hb with hb | hb
          · exact hb ▸ hlt
          · exact Nat.lt_trans hlt (ha b hb)
        · rename_i hne hnl
          have hgt : a.1 < k := by
            rcases Nat.lt_or_ge a.1 k with h' | h'
            · exact h'
            · exact absurd (Nat.le_antisymm (Nat.not_lt.mp hnl) h').symm (by simpa using hne)
          refine List.pairwise_cons.mpr ⟨?_, ih hm⟩
          intro b hb
          rcases insertRec_mem hb with hb | hb
          · exact ha b hb
          · exact hb ▸ hgt

theorem insertRec_append_left {a b : List (Nat × ByteArray)} {k : Nat} {v : ByteArray}
    (h : ∀ kv ∈ a, kv.1 < k) : insertRec (a ++ b) k v = a ++ insertRec b k v := by
  induction a with
  | nil => rfl
  | cons x a ih =>
      have hx : x.1 < k := h x (List.mem_cons_self ..)
      rw [List.cons_append, insertRec]
      rw [if_neg (by simp; exact Nat.ne_of_gt hx), if_neg (Nat.not_lt.mpr (Nat.le_of_lt hx))]
      rw [ih (fun kv hkv => h kv (List.mem_cons_of_mem _ hkv))]
      rfl

theorem insertRec_head {b : List (Nat × ByteArray)} {k : Nat} {v : ByteArray}
    (h : ∀ kv ∈ b, k < kv.1) : insertRec b k v = (k, v) :: b := by
  cases b with
  | nil => rfl
  | cons x b =>
      have hx : k < x.1 := h x (List.mem_cons_self ..)
      rw [insertRec, if_neg (by simp; exact Nat.ne_of_lt hx), if_pos hx]

theorem insertRec_append_right {a b : List (Nat × ByteArray)} {k : Nat} {v : ByteArray}
    (h : ∀ kv ∈ b, k < kv.1) : insertRec (a ++ b) k v = insertRec a k v ++ b := by
  induction a with
  | nil => exact insertRec_head h
  | cons x a ih =>
      rw [List.cons_append, insertRec, insertRec]
      split
      · rfl
      · split
        · rfl
        · rw [ih]; rfl

end RaftKV.BTree

namespace RaftKV.BTree

/-! ## Insertion: the pieces -/

/-- A page holding node `n` denotes `m`. -/
def NodeDen (pages : Pages) (lim d : Nat) (lo hi : Option Nat)
    (n : Node) (m : List (Nat × ByteArray)) : Prop :=
  ∀ p, p < lim → pages p = some n → Denote pages lim d lo hi p m

/-- What a correct descent returns: one page holding `m`, or two and a separator. -/
def InsOK (pages : Pages) (lim d : Nat) (lo hi : Option Nat)
    (r : Ins) (m : List (Nat × ByteArray)) : Prop :=
  match r with
  | .ok q => Denote pages lim d lo hi q m
  | .split l s rp => ∃ m1 m2, m = m1 ++ m2 ∧
      Denote pages lim d lo (some s) l m1 ∧
      Denote pages lim d (some s) hi rp m2 ∧ SepIn lo hi s

/-- `emit` writes what it was given, and the pages it wrote hold it. -/
theorem emit_correct {f : Pages} {a a' : Alloc} {n : Node} {r : Ins} {d : Nat}
    {sp : Unit → Option (Node × Nat × Node)} {lo hi : Option Nat} {m : List (Nat × ByteArray)}
    (h : emit a n sp = some (r, a'))
    (hn : NodeDen (patch f a'.writes) a'.next d lo hi n m)
    (hsp : ∀ nl s nr, sp () = some (nl, s, nr) → ∃ m1 m2, m = m1 ++ m2 ∧
        NodeDen (patch f a'.writes) a'.next d lo (some s) nl m1 ∧
        NodeDen (patch f a'.writes) a'.next d (some s) hi nr m2 ∧ SepIn lo hi s) :
    InsOK (patch f a'.writes) a'.next d lo hi r m := by
  unfold emit at h
  split at h
  · injection h with h; injection h with hr ha; subst hr; subst ha
    exact hn _ (Nat.lt_succ_self _) (patch_push f a n)
  · split at h
    · exact absurd h (by simp)
    · rename_i nl sep nr hsome
      split at h
      · injection h with h; injection h with hr ha; subst hr; subst ha
        obtain ⟨m1, m2, hm, h1, h2, hsep⟩ := hsp nl sep nr hsome
        refine ⟨m1, m2, hm, ?_, ?_, hsep⟩
        · exact h1 _ (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _))
            (patch_push_two f a nl nr)
        · exact h2 _ (Nat.lt_succ_self _) (patch_push f _ nr)
      · exact absurd h (by simp)

/-! ### Splitting a leaf -/

theorem splitLeaf_correct {recs : List (Nat × ByteArray)} {nl nr : Node} {sep : Nat}
    {lo hi : Option Nat} {pages : Pages} {lim : Nat}
    (hs : Sorted recs) (hr : ∀ kv ∈ recs, InRange lo hi kv.1)
    (h : splitLeaf recs = some (nl, sep, nr)) :
    ∃ m1 m2, recs = m1 ++ m2 ∧
      NodeDen pages lim 0 lo (some sep) nl m1 ∧
      NodeDen pages lim 0 (some sep) hi nr m2 ∧ SepIn lo hi sep := by
  unfold splitLeaf at h
  split at h
  · exact absurd h (by simp)
  · rename_i r rs hdrop
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    subst h1; subst h2; subst h3
    refine ⟨recs.take (recs.length / 2), r :: rs, ?_, ?_, ?_, ?_⟩
    · rw [← hdrop, List.take_append_drop]
    · -- the left half: sorted, and everything in it is below the promoted key
      intro p hp hpage
      have hsplit : Sorted (recs.take (recs.length / 2)) ∧ Sorted (r :: rs) ∧
          ∀ a ∈ recs.take (recs.length / 2), ∀ b ∈ r :: rs, a.1 < b.1 := by
        have := List.pairwise_append.mp
          (show Sorted (recs.take (recs.length / 2) ++ (r :: rs)) by
            rw [← hdrop, List.take_append_drop]; exact hs)
        exact this
      refine Denote.leaf hp hpage (by rw [List.toList_toArray]; exact hsplit.1) ?_
      rw [List.toList_toArray]
      intro kv hkv
      exact ⟨(hr kv (List.mem_of_mem_take hkv)).1,
        hsplit.2.2 kv hkv r (List.mem_cons_self ..)⟩
    · -- the right half: everything in it is at or above the promoted key
      intro p hp hpage
      have hsr : Sorted (r :: rs) := by
        rw [← hdrop]; exact List.Pairwise.sublist (List.drop_sublist _ _) hs
      refine Denote.leaf hp hpage (by rw [List.toList_toArray]; exact hsr) ?_
      rw [List.toList_toArray]
      intro kv hkv
      have hmem : kv ∈ recs := hdrop ▸ hkv |> List.mem_of_mem_drop
      refine ⟨?_, (hr kv hmem).2⟩
      rcases List.mem_cons.mp hkv with he | hin
      · exact Nat.le_of_eq (congrArg Prod.fst he).symm
      · exact Nat.le_of_lt ((List.pairwise_cons.mp hsr).1 kv hin)
    · have hmem : r ∈ recs := hdrop ▸ (List.mem_cons_self ..) |> List.mem_of_mem_drop
      exact ⟨(hr r hmem).1, HiLe.of_hi (hr r hmem).2⟩

end RaftKV.BTree

namespace RaftKV.BTree

/-! ### Splitting a branch -/

theorem chain_split {pages : Pages} {lim d : Nat} :
    ∀ {lo hi : Option Nat} {ks cs : List Nat} {m : List (Nat × ByteArray)},
      Chain pages lim d lo hi ks cs m →
      ∀ (j : Nat) {sep : Nat} {right : List Nat}, ks.drop j = sep :: right →
      ∃ m1 m2, m = m1 ++ m2 ∧
        Chain pages lim d lo (some sep) (ks.take j) (cs.take (j + 1)) m1 ∧
        Chain pages lim d (some sep) hi right (cs.drop (j + 1)) m2 ∧ SepIn lo hi sep := by
  intro lo hi ks
  induction ks generalizing lo with
  | nil => intro cs m hc j sep right hd; exact absurd hd (by simp)
  | cons s ks ih =>
      intro cs m hc j sep right hdrop
      cases hc with
      | @cons _ _ c _ _ _ cs mc ms hd hs hrest =>
        cases j with
        | zero =>
            simp only [List.drop_zero, List.cons.injEq] at hdrop
            obtain ⟨hsep, hright⟩ := hdrop
            subst hsep; subst hright
            exact ⟨mc, ms, rfl, .one hd, hrest, hs⟩
        | succ j =>
            obtain ⟨ms1, ms2, hms, hl, hr, hsep⟩ := ih hrest j (by simpa using hdrop)
            refine ⟨mc ++ ms1, ms2, by rw [hms, List.append_assoc], ?_, hr, ?_⟩
            · exact .cons hd ⟨hs.1, hsep.1⟩ hl
            · exact ⟨Lo.mono hs.1 hsep.1, hsep.2⟩

theorem splitBranch_correct {pages : Pages} {lim d : Nat} {lo hi : Option Nat}
    {ks cs : List Nat} {m : List (Nat × ByteArray)} (hc : Chain pages lim d lo hi ks cs m)
    {nl nr : Node} {sep : Nat} (h : splitBranch ks cs = some (nl, sep, nr)) :
    ∃ m1 m2, m = m1 ++ m2 ∧
      NodeDen pages lim (d + 1) lo (some sep) nl m1 ∧
      NodeDen pages lim (d + 1) (some sep) hi nr m2 ∧ SepIn lo hi sep := by
  unfold splitBranch at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  · rename_i s' right hdrop
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    subst h1; subst h2; subst h3
    obtain ⟨m1, m2, hm, hl, hr, hsep⟩ := chain_split hc (ks.length / 2) hdrop
    refine ⟨m1, m2, hm, ?_, ?_, hsep⟩
    · intro p hp hpage
      exact Denote.branch hp hpage (by rw [List.toList_toArray, List.toList_toArray]; exact hl)
    · intro p hp hpage
      exact Denote.branch hp hpage (by rw [List.toList_toArray, List.toList_toArray]; exact hr)

end RaftKV.BTree

namespace RaftKV.BTree

theorem insAt_zero {α : Type} (l : List α) (x : α) : insAt l 0 x = x :: l := by
  cases l <;> rfl

/-- The child index a descent takes, on lists. -/
def cidx (ks : List Nat) (k : Nat) : Nat := (ks.filter (fun s => s ≤ k)).length

theorem childIndex_cidx (keys : Array Nat) (k : Nat) :
    childIndex keys k = cidx keys.toList k := rfl

/-- The branch a descent rebuilds: one child replaced, or one child become two. -/
def ChainIns (pages : Pages) (lim d : Nat) (lo hi : Option Nat)
    (ks cs : List Nat) (i : Nat) (r : Ins) (m : List (Nat × ByteArray)) : Prop :=
  match r with
  | .ok q => Chain pages lim d lo hi ks (setAt cs i q) m
  | .split l s rp =>
      Chain pages lim d lo hi (insAt ks i s) (insAt (setAt cs i l) (i + 1) rp) m

/--
Rebuilding a branch after its search-path child was updated.

The separators localise `k` to one child, so the branch's new contents are the
old ones with that child's segment updated — which, because the segment sits
between keys that bracket `k`, is exactly `insertRec` applied to the whole.
-/
theorem chain_insert {pages₀ pages : Pages} {lim₀ lim d k : Nat} {v : ByteArray}
    (hf : ∀ q, q < lim₀ → pages q = pages₀ q) (hl : lim₀ ≤ lim) {r : Ins} :
    ∀ {lo hi : Option Nat} {ks cs : List Nat} {m : List (Nat × ByteArray)},
      Chain pages₀ lim₀ d lo hi ks cs m → InRange lo hi k →
      (∀ lo' hi' c mi, cs[cidx ks k]? = some c → Denote pages₀ lim₀ d lo' hi' c mi →
        InRange lo' hi' k → InsOK pages lim d lo' hi' r (insertRec mi k v)) →
      ChainIns pages lim d lo hi ks cs (cidx ks k) r (insertRec m k v) := by
  intro lo hi ks
  induction ks generalizing lo with
  | nil =>
    intro cs m hc hk hchild
    cases hc with
    | @one _ c _ _ m hd =>
      have hres := hchild lo hi c m rfl hd hk
      cases r with
      | ok q => exact .one hres
      | split l s rp =>
          obtain ⟨m1, m2, hm, h1, h2, hsep⟩ := hres
          show Chain pages lim d lo hi [s] [l, rp] _
          rw [hm]
          exact .cons h1 hsep (.one h2)
  | cons s ks ih =>
    intro cs m hc hk hchild
    cases hc with
    | @cons _ _ c _ _ _ cs mc ms hd hs hrest =>
      by_cases hsk : s ≤ k
      · -- `k` belongs to the right of this separator
        have hcidx : cidx (s :: ks) k = cidx ks k + 1 := by
          simp [cidx, hsk, Nat.add_comm]
        have hsplit : insertRec (mc ++ ms) k v = mc ++ insertRec ms k v :=
          insertRec_append_left (fun kv hkv =>
            Nat.lt_of_lt_of_le (denote_range _ hd kv hkv).2 hsk)
        have hk' : InRange (some s) hi k := ⟨hsk, hk.2⟩
        have hrec := ih hrest hk' (fun lo' hi' c' mi hc' hden hk'' =>
          hchild lo' hi' c' mi (by rw [hcidx]; simpa using hc') hden hk'')
        have hdf : Denote pages lim d lo (some s) c mc := denote_frame hf hl _ hd
        rw [hcidx, hsplit]
        cases r with
        | ok q => exact .cons hdf hs hrec
        | split l sep rp => exact .cons hdf hs hrec
      · -- `k` belongs to this child, and to no other
        have hks' : List.filter (fun s => decide (s ≤ k)) ks = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx
          simp only [decide_eq_true_eq]
          exact Nat.not_le.mpr (Nat.lt_of_lt_of_le (Nat.not_le.mp hsk) (chain_keys hrest x hx).1)
        have hcidx : cidx (s :: ks) k = 0 := by simp [cidx, hsk, hks']
        have hsplit : insertRec (mc ++ ms) k v = insertRec mc k v ++ ms :=
          insertRec_append_right (fun kv hkv =>
            Nat.lt_of_lt_of_le (Nat.not_le.mp hsk)
              (chain_range (fun _ _ q m' hq => denote_range _ hq) hrest kv hkv).1)
        have hres := hchild lo (some s) c mc (by rw [hcidx]; rfl) hd ⟨hk.1, Nat.not_le.mp hsk⟩
        have hrf : Chain pages lim d (some s) hi ks cs ms :=
          chain_frame (fun _ _ q m' hq => denote_frame hf hl _ hq) hrest
        rw [hcidx, hsplit]
        cases r with
        | ok q => exact .cons hres hs hrf
        | split l sep rp =>
            obtain ⟨m1, m2, hm, h1, h2, hsep⟩ := hres
            show Chain pages lim d lo hi (sep :: s :: ks) (l :: insAt cs 0 rp) _
            rw [insAt_zero, hm, List.append_assoc]
            refine .cons h1 ⟨hsep.1, HiLe.mono hs.2 hsep.2⟩ (.cons h2 ⟨hsep.2, hs.2⟩ hrf)

end RaftKV.BTree

namespace RaftKV.BTree

/--
**P4 for writes, at the level of one descent.**

Starting from a subtree denoting `m`, a successful descent produces pages
denoting `insertRec m k v` — one binding added or replaced, and nothing else
disturbed — under the image the commit has built so far.
-/
theorem insertAux_correct {t : Tree} {pages₀ : Pages} {lim₀ : Nat} (ht : t.next = lim₀)
    {k : Nat} {v : ByteArray} :
    ∀ (fuel : Nat) {d : Nat},
    ∀ {lo hi : Option Nat} {p : Nat} {m : List (Nat × ByteArray)} {a a' : Alloc} {r : Ins},
      Denote pages₀ lim₀ d lo hi p m → InRange lo hi k →
      Alloc.Grows lim₀ a →
      insertAux t pages₀ k v fuel p a = some (r, a') →
      InsOK (patch pages₀ a'.writes) a'.next d lo hi r (insertRec m k v) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ h; exact absurd h (by simp [insertAux])
  | succ fuel ih =>
    intro d lo hi p m a a' r hden hk hg h
    rw [insertAux] at h
    have hgrow : Alloc.Grows lim₀ a' := insertAux_grows (fuel + 1) p (by rw [insertAux]; exact h) hg
    have hbelow : ∀ q, q < lim₀ → patch pages₀ a'.writes q = pages₀ q :=
      patch_below a'.writes (fun w hw => (hgrow.mem w hw).1)
    cases hden with
    | @leaf p recs lo hi hp hpage hs hr =>
        rw [get_of_lt ht hp, hpage] at h
        dsimp only at h
        refine emit_correct h ?_ ?_
        · intro p' hp' hpage'
          refine Denote.leaf hp' hpage' (by rw [List.toList_toArray]; exact insertRec_sorted hs) ?_
          rw [List.toList_toArray]
          intro kv hkv
          rcases insertRec_mem hkv with h' | h'
          · exact hr kv h'
          · exact h' ▸ hk
        · intro nl sep nr hsome
          exact splitLeaf_correct (insertRec_sorted hs)
            (fun kv hkv => by
              rcases insertRec_mem hkv with h' | h'
              · exact hr kv h'
              · exact h' ▸ hk)
            hsome
    | @branch d' p keys children lo hi m hp hpage hchain =>
        rw [get_of_lt ht hp, hpage] at h
        dsimp only at h
        split at h
        · exact absurd h (by simp)
        · rename_i c hchild
          have hcidx : children.toList[cidx keys.toList k]? = some c := by
            rw [Array.getElem?_toList, ← childIndex_cidx]; exact hchild
          split at h
          · exact absurd h (by simp)
          · -- the child fitted in one page
            rename_i q a2 hrec
            have hg2 : Alloc.Grows lim₀ a2 := insertAux_grows fuel c hrec hg
            have hext : Alloc.Extends a2 a' := emit_extends h
            have hframe : ∀ x, x < a2.next → patch pages₀ a'.writes x = patch pages₀ a2.writes x :=
              patch_extends hext
            have hb2 : ∀ x, x < lim₀ → patch pages₀ a2.writes x = pages₀ x :=
              patch_below a2.writes (fun w hw => (hg2.mem w hw).1)
            have hci := chain_insert (v := v) hb2 hg2.le hchain hk
              (fun lo' hi' c' mi hc' hden' hk' => by
                have : c' = c := by rw [hcidx] at hc'; injection hc' with he; exact he.symm
                subst this
                exact ih hden' hk' hg hrec)
            have hci' : Chain (patch pages₀ a'.writes) a'.next d' lo hi keys.toList
                (setAt children.toList (cidx keys.toList k) q) (insertRec m k v) :=
              chain_frame (fun _ _ x m' hx => denote_frame hframe hext.le _ hx) hci
            refine emit_correct h (fun p' hp' hpage' => ?_) (fun nl sep nr hsome => ?_)
            · exact Denote.branch hp' hpage'
                (by rw [List.toList_toArray, List.toList_toArray]; exact hci')
            · exact splitBranch_correct hci' hsome
          · -- the child split in two
            rename_i lq sep rq a2 hrec
            have hg2 : Alloc.Grows lim₀ a2 := insertAux_grows fuel c hrec hg
            have hext : Alloc.Extends a2 a' := emit_extends h
            have hframe : ∀ x, x < a2.next → patch pages₀ a'.writes x = patch pages₀ a2.writes x :=
              patch_extends hext
            have hb2 : ∀ x, x < lim₀ → patch pages₀ a2.writes x = pages₀ x :=
              patch_below a2.writes (fun w hw => (hg2.mem w hw).1)
            have hci := chain_insert (v := v) hb2 hg2.le hchain hk
              (fun lo' hi' c' mi hc' hden' hk' => by
                have : c' = c := by rw [hcidx] at hc'; injection hc' with he; exact he.symm
                subst this
                exact ih hden' hk' hg hrec)
            have hci' : Chain (patch pages₀ a'.writes) a'.next d' lo hi
                (insAt keys.toList (cidx keys.toList k) sep)
                (insAt (setAt children.toList (cidx keys.toList k) lq)
                  (cidx keys.toList k + 1) rq) (insertRec m k v) :=
              chain_frame (fun _ _ x m' hx => denote_frame hframe hext.le _ hx) hci
            refine emit_correct h (fun p' hp' hpage' => ?_) (fun nl sep' nr hsome => ?_)
            · exact Denote.branch hp' hpage'
                (by rw [List.toList_toArray, List.toList_toArray]; exact hci')
            · exact splitBranch_correct hci' hsome

end RaftKV.BTree

namespace RaftKV.BTree

/--
**P4 for writes.**

A successful insert produces a root cell denoting the old contents with `k ↦ v`
added or replaced, over the image the commit writes. The depth grows by at most
one — the tree gets taller only when the root itself splits — which is the only
thing standing between this and a fixed search fuel.
-/
theorem insert_correct {t t' : Tree} {pages : Pages} {m : List (Nat × ByteArray)}
    {k : Nat} {v : ByteArray} {ws : List (Nat × Node)} {d : Nat}
    (hwf : WFd t pages d m) (hd : d < maxDepth)
    (h : t.insert pages k v = some (t', ws)) :
    ∃ d', d' ≤ d + 1 ∧ WFd t' (patch pages ws) d' (insertRec m k v) := by
  unfold WFd at hwf
  unfold Tree.insert at h
  split at h
  · -- the tree was empty: one fresh leaf
    rename_i he
    rw [he] at hwf
    subst hwf
    dsimp only at h
    split at h
    · injection h with h; injection h with h1 h2
      subst h1; subst h2
      refine ⟨0, Nat.zero_le _, ?_⟩
      show Denote _ _ 0 none none t.next _
      refine Denote.leaf (Nat.lt_succ_self _)
        (patch_push pages ⟨t.next, []⟩ (Node.leaf #[(k, v)])) ?_ ?_
      · exact List.pairwise_singleton ..
      · intro kv _; exact ⟨trivial, trivial⟩
    · exact absurd h (by simp)
  · rename_i r he
    rw [he] at hwf
    split at h
    · exact absurd h (by simp)
    · -- the root still fits in one page
      rename_i q a hrec
      injection h with h; injection h with h1 h2
      subst h1; subst h2
      exact ⟨d, Nat.le_succ _,
        insertAux_correct rfl maxDepth hwf ⟨trivial, trivial⟩ (Alloc.grows_init _) hrec⟩
    · -- the root split, so the tree gained a level
      rename_i lq sep rq a hrec
      injection h with h; injection h with h1 h2
      subst h1; subst h2
      obtain ⟨m1, m2, hm, h1, h2, _⟩ :=
        insertAux_correct (t := t) rfl maxDepth hwf ⟨trivial, trivial⟩ (Alloc.grows_init _) hrec
      refine ⟨d + 1, Nat.le_refl _, ?_⟩
      show Denote _ _ (d + 1) none none a.next _
      have hext : Alloc.Extends a (a.push (Node.branch #[sep] #[lq, rq])).2 :=
        Alloc.extends_push
      have hframe : ∀ x, x < a.next →
          patch pages (a.push (Node.branch #[sep] #[lq, rq])).2.writes x
            = patch pages a.writes x := patch_extends hext
      refine Denote.branch (Nat.lt_succ_self _)
        (patch_push pages a (Node.branch #[sep] #[lq, rq])) ?_
      rw [hm]
      exact .cons (denote_frame hframe hext.le _ h1) ⟨trivial, trivial⟩
        (.one (denote_frame hframe hext.le _ h2))

/-- The same, kept inside the search fuel. -/
theorem insert_wf {t t' : Tree} {pages : Pages} {m : List (Nat × ByteArray)}
    {k : Nat} {v : ByteArray} {ws : List (Nat × Node)} {d : Nat}
    (hwf : WFd t pages d m) (hd : d + 1 < maxDepth)
    (h : t.insert pages k v = some (t', ws)) :
    WF t' (patch pages ws) (insertRec m k v) := by
  obtain ⟨d', hle, hden⟩ := insert_correct hwf (Nat.lt_of_succ_lt hd) h
  exact ⟨d', Nat.lt_of_le_of_lt hle hd, hden⟩

end RaftKV.BTree

namespace RaftKV.BTree

/-! ## Deletion

Simpler than insertion in every way: nothing splits, so the depth is unchanged
and the rebuilt branch has the same shape. Nothing is merged either — a node may
be left underfull, which the invariant permits because it says nothing about how
full a node is.
-/

theorem eraseRec_mem {m : List (Nat × ByteArray)} {k : Nat} {kv : Nat × ByteArray} :
    kv ∈ eraseRec m k → kv ∈ m := by
  induction m with
  | nil => intro h; exact h
  | cons a m ih =>
      intro h
      rw [eraseRec] at h
      split at h
      · exact List.mem_cons_of_mem _ h
      · rcases List.mem_cons.mp h with h' | h'
        · exact h' ▸ List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih h')

theorem eraseRec_sorted {m : List (Nat × ByteArray)} {k : Nat}
    (h : Sorted m) : Sorted (eraseRec m k) := by
  induction m with
  | nil => exact List.Pairwise.nil
  | cons a m ih =>
      obtain ⟨ha, hm⟩ := List.pairwise_cons.mp h
      rw [eraseRec]
      split
      · exact hm
      · exact List.pairwise_cons.mpr ⟨fun b hb => ha b (eraseRec_mem hb), ih hm⟩

theorem eraseRec_append_left {a b : List (Nat × ByteArray)} {k : Nat}
    (h : ∀ kv ∈ a, kv.1 < k) : eraseRec (a ++ b) k = a ++ eraseRec b k := by
  induction a with
  | nil => rfl
  | cons x a ih =>
      have hx : x.1 < k := h x (List.mem_cons_self ..)
      rw [List.cons_append, eraseRec, if_neg (by simp; exact (Nat.ne_of_lt hx).symm)]
      rw [ih (fun kv hkv => h kv (List.mem_cons_of_mem _ hkv))]
      rfl

theorem eraseRec_none {b : List (Nat × ByteArray)} {k : Nat}
    (h : ∀ kv ∈ b, k < kv.1) : eraseRec b k = b := by
  induction b with
  | nil => rfl
  | cons x b ih =>
      have hx : k < x.1 := h x (List.mem_cons_self ..)
      rw [eraseRec, if_neg (by simp; exact Nat.ne_of_lt hx)]
      rw [ih (fun kv hkv => h kv (List.mem_cons_of_mem _ hkv))]

theorem eraseRec_append_right {a b : List (Nat × ByteArray)} {k : Nat}
    (h : ∀ kv ∈ b, k < kv.1) : eraseRec (a ++ b) k = eraseRec a k ++ b := by
  induction a with
  | nil => rw [List.nil_append, eraseRec_none h]; rfl
  | cons x a ih =>
      rw [List.cons_append, eraseRec, eraseRec]
      split
      · rfl
      · rw [ih]; rfl

/-- Rebuilding a branch after its search-path child was rewritten. -/
theorem chain_erase {pages₀ pages : Pages} {lim₀ lim d k : Nat}
    (hf : ∀ q, q < lim₀ → pages q = pages₀ q) (hl : lim₀ ≤ lim) {q : Nat} :
    ∀ {lo hi : Option Nat} {ks cs : List Nat} {m : List (Nat × ByteArray)},
      Chain pages₀ lim₀ d lo hi ks cs m →
      (∀ lo' hi' c mi, cs[cidx ks k]? = some c → Denote pages₀ lim₀ d lo' hi' c mi →
        Denote pages lim d lo' hi' q (eraseRec mi k)) →
      Chain pages lim d lo hi ks (setAt cs (cidx ks k) q) (eraseRec m k) := by
  intro lo hi ks
  induction ks generalizing lo with
  | nil =>
    intro cs m hc hchild
    cases hc with
    | @one _ c _ _ m hd => exact .one (hchild lo hi c m rfl hd)
  | cons s ks ih =>
    intro cs m hc hchild
    cases hc with
    | @cons _ _ c _ _ _ cs mc ms hd hs hrest =>
      by_cases hsk : s ≤ k
      · have hcidx : cidx (s :: ks) k = cidx ks k + 1 := by simp [cidx, hsk, Nat.add_comm]
        have hsplit : eraseRec (mc ++ ms) k = mc ++ eraseRec ms k :=
          eraseRec_append_left (fun kv hkv =>
            Nat.lt_of_lt_of_le (denote_range _ hd kv hkv).2 hsk)
        rw [hcidx, hsplit]
        exact .cons (denote_frame hf hl _ hd) hs
          (ih hrest (fun lo' hi' c' mi hc' hden =>
            hchild lo' hi' c' mi (by rw [hcidx]; simpa using hc') hden))
      · have hks' : List.filter (fun s => decide (s ≤ k)) ks = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx
          simp only [decide_eq_true_eq]
          exact Nat.not_le.mpr (Nat.lt_of_lt_of_le (Nat.not_le.mp hsk) (chain_keys hrest x hx).1)
        have hcidx : cidx (s :: ks) k = 0 := by simp [cidx, hsk, hks']
        have hsplit : eraseRec (mc ++ ms) k = eraseRec mc k ++ ms :=
          eraseRec_append_right (fun kv hkv =>
            Nat.lt_of_lt_of_le (Nat.not_le.mp hsk)
              (chain_range (fun _ _ x m' hx => denote_range _ hx) hrest kv hkv).1)
        rw [hcidx, hsplit]
        exact .cons (hchild lo (some s) c mc (by rw [hcidx]; rfl) hd) hs
          (chain_frame (fun _ _ x m' hx => denote_frame hf hl _ hx) hrest)

/-- **P4 for deletion, at the level of one descent.** -/
theorem eraseAux_correct {t : Tree} {pages₀ : Pages} {lim₀ : Nat} (ht : t.next = lim₀)
    {k : Nat} :
    ∀ (fuel : Nat) {d : Nat},
    ∀ {lo hi : Option Nat} {p : Nat} {m : List (Nat × ByteArray)} {a a' : Alloc} {q : Nat},
      Denote pages₀ lim₀ d lo hi p m → Alloc.Grows lim₀ a →
      eraseAux t pages₀ k fuel p a = some (q, a') →
      Denote (patch pages₀ a'.writes) a'.next d lo hi q (eraseRec m k) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ _ h; exact absurd h (by simp [eraseAux])
  | succ fuel ih =>
    intro d lo hi p m a a' q hden hg h
    rw [eraseAux] at h
    cases hden with
    | @leaf p recs lo hi hp hpage hs hr =>
        rw [get_of_lt ht hp, hpage] at h
        dsimp only at h
        injection h with h; injection h with h1 h2
        subst h1; subst h2
        refine Denote.leaf (Nat.lt_succ_self _) (patch_push pages₀ a _)
          (by rw [List.toList_toArray]; exact eraseRec_sorted hs) ?_
        rw [List.toList_toArray]
        exact fun kv hkv => hr kv (eraseRec_mem hkv)
    | @branch d' p keys children lo hi m hp hpage hchain =>
        rw [get_of_lt ht hp, hpage] at h
        dsimp only at h
        split at h
        · exact absurd h (by simp)
        · rename_i c hchild
          have hcidx : children.toList[cidx keys.toList k]? = some c := by
            rw [Array.getElem?_toList, ← childIndex_cidx]; exact hchild
          split at h
          · exact absurd h (by simp)
          · rename_i q2 a2 hrec
            injection h with h; injection h with h1 h2
            subst h1; subst h2
            have hg2 : Alloc.Grows lim₀ a2 := eraseAux_grows fuel c hrec hg
            have hext : Alloc.Extends a2 (a2.push (Node.branch keys
                (setAt children.toList (childIndex keys k) q2).toArray)).2 :=
              Alloc.extends_push
            have hframe : ∀ x, x < a2.next →
                patch pages₀ (a2.push (Node.branch keys
                  (setAt children.toList (childIndex keys k) q2).toArray)).2.writes x
                  = patch pages₀ a2.writes x := patch_extends hext
            have hb2 : ∀ x, x < lim₀ → patch pages₀ a2.writes x = pages₀ x :=
              patch_below a2.writes (fun w hw => (hg2.mem w hw).1)
            have hce := chain_erase (q := q2) hb2 hg2.le hchain
              (fun lo' hi' c' mi hc' hden' => by
                have : c' = c := by rw [hcidx] at hc'; injection hc' with he; exact he.symm
                subst this
                exact ih hden' hg hrec)
            refine Denote.branch (Nat.lt_succ_self _) (patch_push pages₀ a2 _) ?_
            rw [List.toList_toArray, List.toList_toArray]
            exact chain_frame (fun _ _ x m' hx => denote_frame hframe hext.le _ hx) hce

/-- **P4 for deletion.** The binding goes, the depth does not change. -/
theorem erase_correct {t t' : Tree} {pages : Pages} {m : List (Nat × ByteArray)}
    {k : Nat} {ws : List (Nat × Node)} {d : Nat}
    (hwf : WFd t pages d m) (h : t.erase pages k = some (t', ws)) :
    WFd t' (patch pages ws) d (eraseRec m k) := by
  unfold WFd at hwf
  unfold Tree.erase at h
  split at h
  · rename_i he
    rw [he] at hwf
    subst hwf
    injection h with h; injection h with h1 h2
    subst h1; subst h2
    unfold WFd
    rw [he]
    rfl
  · rename_i r he
    rw [he] at hwf
    split at h
    · exact absurd h (by simp)
    · rename_i q a hrec
      injection h with h; injection h with h1 h2
      subst h1; subst h2
      exact eraseAux_correct rfl maxDepth hwf (Alloc.grows_init _) hrec

/-- Deletion keeps the tree inside the search fuel. -/
theorem erase_wf {t t' : Tree} {pages : Pages} {m : List (Nat × ByteArray)}
    {k : Nat} {ws : List (Nat × Node)}
    (hwf : WF t pages m) (h : t.erase pages k = some (t', ws)) :
    WF t' (patch pages ws) (eraseRec m k) := by
  obtain ⟨d, hd, hden⟩ := hwf
  exact ⟨d, hd, erase_correct hden h⟩

end RaftKV.BTree

namespace RaftKV.BTree

/--
**The B-tree, end to end.**

One commit, and everything the four properties give, in one statement. Starting
from a tree holding `m`:

1. the new root cell reads back `m` with `k ↦ v` inserted — every key, and the
   whole ordered scan (P4);
2. and *whatever the crash did*, the old root cell reads back `m` unchanged.
   Any image agreeing with the pre-commit one below the old high-water mark, so
   arbitrary garbage in the whole range the commit was allocating; any subset of
   the commit's page writes having reached the platter, in any order (P1–P3).

Clause 2 is the one that matters for durability: the commit point is the root
cell, and until it moves the tree on disk is exactly the tree that was there
before, byte for byte. Clause 1 is what makes the store worth committing to.
-/
theorem insert_commit {t t' : Tree} {pages : Pages} {m : List (Nat × ByteArray)}
    {k : Nat} {v : ByteArray} {ws : List (Nat × Node)} {d : Nat}
    (hwf : WFd t pages d m) (hd : d + 1 < maxDepth)
    (h : t.insert pages k v = some (t', ws)) :
    (∀ k', t'.lookup (patch pages ws) k' = lookupList (insertRec m k v) k')
      ∧ t'.toList (patch pages ws) = insertRec m k v
      ∧ ∀ (g : Pages), (∀ q, q < t.next → g q = pages q) →
          ∀ (ws' : List (Nat × Node)), (∀ w ∈ ws', w ∈ ws) →
            (∀ k', t.lookup (patch g ws') k' = lookupList m k')
              ∧ t.toList (patch g ws') = m := by
  have hwf' : WF t' (patch pages ws) (insertRec m k v) := insert_wf hwf hd h
  have hold : WF t pages m := ⟨d, Nat.lt_of_succ_lt hd, hwf⟩
  refine ⟨fun k' => lookup_correct hwf', toList_correct hwf', fun g hg ws' hsub => ?_⟩
  obtain ⟨hl, ht⟩ := insert_crash_safe h g hg ws' hsub
  exact ⟨fun k' => (hl k').trans (lookup_correct hold), ht.trans (toList_correct hold)⟩

/-! ## Batches -/

/-- Lookup, one cell at a time. -/
theorem lookupList_nil (k : Nat) : lookupList [] k = none := rfl

theorem lookupList_cons (k₀ : Nat) (v₀ : ByteArray) (rs : List (Nat × ByteArray)) (k' : Nat) :
    lookupList ((k₀, v₀) :: rs) k' = if k₀ = k' then some v₀ else lookupList rs k' := by
  unfold lookupList
  rw [List.find?_cons]
  by_cases h : k₀ = k'
  · subst h; simp
  · rw [if_neg h]
    have : (k₀ == k') = false := by simpa using h
    rw [this]

/-- A key below everything in a sorted list is not in it. -/
theorem lookupList_of_lt : ∀ {m : List (Nat × ByteArray)} {k : Nat},
    Sorted m → (∀ q ∈ m, k < q.1) → lookupList m k = none
  | [], _, _, _ => rfl
  | (k₀, v₀) :: rs, k, hs, hlt => by
      rw [lookupList_cons, if_neg (by have := hlt _ (List.mem_cons_self ..); omega)]
      exact lookupList_of_lt (sorted_tail hs)
        (fun q hq => hlt q (List.mem_cons_of_mem _ hq))

/-- Inserting changes the lookup at that key and nothing else, on a sorted list. -/
theorem lookupList_insertRec : ∀ (m : List (Nat × ByteArray)) (k : Nat) (v : ByteArray),
    Sorted m → ∀ k', lookupList (insertRec m k v) k'
      = if k' = k then some v else lookupList m k'
  | [], k, v, _, k' => by
      rw [insertRec, lookupList_cons, lookupList_nil]
      by_cases h : k' = k
      · subst h; simp
      · rw [if_neg (fun hq : k = k' => h hq.symm), if_neg h]
  | (k₀, v₀) :: rs, k, v, hs, k' => by
      rw [insertRec]
      by_cases h1 : k == k₀
      · have h1' : k = k₀ := by simpa using h1
        subst h1'
        rw [if_pos h1, lookupList_cons, lookupList_cons]
        by_cases h : k' = k
        · subst h; simp
        · rw [if_neg (fun hq : k = k' => h hq.symm), if_neg (fun hq : k = k' => h hq.symm),
            if_neg h]
      · rw [if_neg h1]
        by_cases h2 : k < k₀
        · rw [if_pos h2, lookupList_cons]
          by_cases h : k' = k
          · subst h; simp
          · rw [if_neg (fun hq : k = k' => h hq.symm), if_neg h]
        · rw [if_neg h2, lookupList_cons, lookupList_cons,
            lookupList_insertRec rs k v (sorted_tail hs) k']
          by_cases h : k₀ = k'
          · subst h
            have hne : ¬ (k₀ = k) := fun hq => h1 (by simp [hq.symm])
            rw [if_pos rfl, if_pos rfl, if_neg (fun hq : k₀ = k => hne hq)]
          · rw [if_neg h, if_neg h]

/-- Deleting removes that key and nothing else, on a sorted list. -/
theorem lookupList_eraseRec : ∀ (m : List (Nat × ByteArray)) (k : Nat),
    Sorted m → ∀ k', lookupList (eraseRec m k) k'
      = if k' = k then none else lookupList m k'
  | [], k, _, k' => by
      rw [eraseRec, lookupList_nil]
      by_cases h : k' = k
      · rw [if_pos h]
      · rw [if_neg h]
  | (k₀, v₀) :: rs, k, hs, k' => by
      rw [eraseRec]
      by_cases h1 : k == k₀
      · have h1' : k = k₀ := by simpa using h1
        subst h1'
        rw [if_pos h1, lookupList_cons]
        by_cases h : k' = k
        · subst h
          rw [if_pos rfl]
          exact lookupList_of_lt (sorted_tail hs) (fun q hq => sorted_head hs q hq)
        · rw [if_neg h, if_neg (fun hq : k = k' => h hq.symm)]
      · rw [if_neg h1, lookupList_cons, lookupList_cons,
          lookupList_eraseRec rs k (sorted_tail hs) k']
        by_cases h : k₀ = k'
        · subst h
          have hne : ¬ (k₀ = k) := fun hq => h1 (by simp [hq])
          rw [if_pos rfl, if_pos rfl, if_neg (fun hq : k₀ = k => hne hq)]
        · rw [if_neg h, if_neg h]

/-- Sortedness survives a batch, which is what makes the two lemmas above apply. -/
theorem applyOps_sorted : ∀ (ops : List Op) (m : List (Nat × ByteArray)),
    Sorted m → Sorted (applyOps m ops)
  | [], m, hs => by rw [applyOps]; exact hs
  | (k, some v) :: ops, m, hs => by
      rw [applyOps]; exact applyOps_sorted ops _ (insertRec_sorted (k := k) (v := v) hs)
  | (k, none) :: ops, m, hs => by
      rw [applyOps]; exact applyOps_sorted ops _ (eraseRec_sorted (k := k) hs)

/-- A batch splits. -/
theorem applyOps_append : ∀ (a b : List Op) (m : List (Nat × ByteArray)),
    applyOps m (a ++ b) = applyOps (applyOps m a) b
  | [], b, m => by rw [List.nil_append, applyOps]
  | (k, some v) :: a, b, m => by
      rw [List.cons_append, applyOps, applyOps, applyOps_append a b]
  | (k, none) :: a, b, m => by
      rw [List.cons_append, applyOps, applyOps, applyOps_append a b]

/-- A batch that never names `k` leaves `k` alone. -/
theorem lookupList_applyOps_notMem : ∀ (ops : List Op) (m : List (Nat × ByteArray)) (k : Nat),
    Sorted m → (∀ o ∈ ops, o.1 ≠ k) → lookupList (applyOps m ops) k = lookupList m k
  | [], m, k, _, _ => by rw [applyOps]
  | (k₀, some v) :: ops, m, k, hs, hne => by
      rw [applyOps, lookupList_applyOps_notMem ops _ k (insertRec_sorted hs)
        (fun o ho => hne o (List.mem_cons_of_mem _ ho)),
        lookupList_insertRec m k₀ v hs k,
        if_neg (fun hq => hne (k₀, some v) (List.mem_cons_self ..) hq.symm)]
  | (k₀, none) :: ops, m, k, hs, hne => by
      rw [applyOps, lookupList_applyOps_notMem ops _ k (eraseRec_sorted hs)
        (fun o ho => hne o (List.mem_cons_of_mem _ ho)),
        lookupList_eraseRec m k₀ hs k,
        if_neg (fun hq => hne (k₀, none) (List.mem_cons_self ..) hq.symm)]

/-- **The last operation naming a key is the one that stands.** -/
theorem lookupList_applyOps_last (pre post : List Op) (m : List (Nat × ByteArray))
    (k : Nat) (ov : Option ByteArray) (hs : Sorted m) (hpost : ∀ o ∈ post, o.1 ≠ k) :
    lookupList (applyOps m (pre ++ (k, ov) :: post)) k = ov := by
  rw [applyOps_append]
  have hs' : Sorted (applyOps m pre) := applyOps_sorted pre m hs
  cases ov with
  | some v =>
      rw [applyOps, lookupList_applyOps_notMem post _ k (insertRec_sorted hs') hpost,
        lookupList_insertRec _ k v hs' k, if_pos rfl]
  | none =>
      rw [applyOps, lookupList_applyOps_notMem post _ k (eraseRec_sorted hs') hpost,
        lookupList_eraseRec _ k hs' k, if_pos rfl]

/--
**A batch is well formed, and no deeper than the inserts in it can make it.**

Each insert adds at most one level, so a batch of `n` operations adds at most
`n`; the fuel bound has to be carried explicitly because `lookup` is bounded by
`maxDepth`.
-/
theorem batch_wf : ∀ (ops : List Op) {t t' : Tree} {pages : Pages}
    {m : List (Nat × ByteArray)} {ws : List (Nat × Node)} {d : Nat},
    WFd t pages d m → d + ops.length < maxDepth →
    t.batch pages ops = some (t', ws) →
    ∃ d', d' ≤ d + ops.length ∧ WFd t' (patch pages ws) d' (applyOps m ops)
  | [], t, t', pages, m, ws, d, hwf, hd, h => by
      rw [Tree.batch] at h
      injection h with h; injection h with h1 h2
      subst h1; subst h2
      exact ⟨d, Nat.le_refl _, by rw [applyOps]; exact hwf⟩
  | (k, ov) :: ops, t, t', pages, m, ws, d, hwf, hd, h => by
      cases ov with
      | some v =>
          rw [Tree.batch] at h
          split at h
          · exact absurd h (by simp)
          · rename_i t₁ ws₁ hins
            split at h
            · exact absurd h (by simp)
            · rename_i t₂ ws₂ hb
              injection h with h; injection h with h1 h2
              subst h1; subst h2
              obtain ⟨d₁, hle₁, hden₁⟩ :=
                insert_correct hwf (by simp at hd; omega) hins
              obtain ⟨d₂, hle₂, hden₂⟩ :=
                batch_wf ops hden₁ (by simp at hd ⊢; omega) hb
              refine ⟨d₂, by simp at hd ⊢; omega, ?_⟩
              rw [patch_append, applyOps]
              exact hden₂
      | none =>
          rw [Tree.batch] at h
          split at h
          · exact absurd h (by simp)
          · rename_i t₁ ws₁ her
            split at h
            · exact absurd h (by simp)
            · rename_i t₂ ws₂ hb
              injection h with h; injection h with h1 h2
              subst h1; subst h2
              have hden₁ := erase_correct hwf her
              obtain ⟨d₂, hle₂, hden₂⟩ :=
                batch_wf ops hden₁ (by simp at hd ⊢; omega) hb
              refine ⟨d₂, by simp at hd ⊢; omega, ?_⟩
              rw [patch_append, applyOps]
              exact hden₂

/--
**One commit, however many keys it touched.**

The new root cell reads back the contents the batch produces — every key, and the
whole ordered scan — while *whatever the crash did*, the old root cell reads back
the old contents unchanged. Any image agreeing with the pre-commit one below the
old mark, so arbitrary garbage in the whole range the batch was allocating; any
subset of its writes having landed, in any order.

This is `insert_commit` for a durable state that is more than one key, which is
what a Raft node's is: the term, the vote, the log window and the snapshot have
to move together or not at all.
-/
theorem batch_commit {t t' : Tree} {pages : Pages} {m : List (Nat × ByteArray)}
    {ops : List Op} {ws : List (Nat × Node)} {d : Nat}
    (hwf : WFd t pages d m) (hd : d + ops.length < maxDepth)
    (h : t.batch pages ops = some (t', ws)) :
    (∀ k', t'.lookup (patch pages ws) k' = lookupList (applyOps m ops) k')
      ∧ t'.toList (patch pages ws) = applyOps m ops
      ∧ ∀ (g : Pages), (∀ q, q < t.next → g q = pages q) →
          ∀ (ws' : List (Nat × Node)), (∀ w ∈ ws', w ∈ ws) →
            (∀ k', t.lookup (patch g ws') k' = lookupList m k')
              ∧ t.toList (patch g ws') = m := by
  obtain ⟨d', hle, hden⟩ := batch_wf ops hwf hd h
  have hwf' : WF t' (patch pages ws) (applyOps m ops) := ⟨d', by omega, hden⟩
  have hold : WF t pages m := ⟨d, by omega, hwf⟩
  refine ⟨fun k' => lookup_correct hwf', toList_correct hwf', fun g hg ws' hsub => ?_⟩
  have hfresh : ∀ w ∈ ws', t.next ≤ w.1 :=
    fun w hw => ((batch_grows ops h).2.1 w (hsub w hw)).1
  have hagree : ∀ q, q < t.next → patch g ws' q = pages q := fun q hq => by
    rw [patch_below ws' hfresh q hq]; exact hg q hq
  exact ⟨fun k' => (lookup_frame hagree).trans (lookup_correct hold),
    (toList_frame hagree).trans (toList_correct hold)⟩

/-- The same for a delete. -/
theorem erase_commit {t t' : Tree} {pages : Pages} {m : List (Nat × ByteArray)}
    {k : Nat} {ws : List (Nat × Node)}
    (hwf : WF t pages m) (h : t.erase pages k = some (t', ws)) :
    (∀ k', t'.lookup (patch pages ws) k' = lookupList (eraseRec m k) k')
      ∧ t'.toList (patch pages ws) = eraseRec m k
      ∧ ∀ (g : Pages), (∀ q, q < t.next → g q = pages q) →
          ∀ (ws' : List (Nat × Node)), (∀ w ∈ ws', w ∈ ws) →
            (∀ k', t.lookup (patch g ws') k' = lookupList m k')
              ∧ t.toList (patch g ws') = m := by
  have hwf' : WF t' (patch pages ws) (eraseRec m k) := erase_wf hwf h
  refine ⟨fun k' => lookup_correct hwf', toList_correct hwf', fun g hg ws' hsub => ?_⟩
  obtain ⟨hl, ht⟩ := erase_crash_safe h g hg ws' hsub
  exact ⟨fun k' => (hl k').trans (lookup_correct hwf), ht.trans (toList_correct hwf)⟩

end RaftKV.BTree
