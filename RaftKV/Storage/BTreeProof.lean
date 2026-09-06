import RaftKV.Storage.BTree

/-!
# What a storage engine owes the layer above it

Four properties, in the order they matter. The first three are about
*durability* — they are what makes a crash survivable, and they are proved here
in full. The fourth is about the data structure being any good, and is the
subject of the second half of this file.

**P1 — Allocation is monotone.** An update never lowers the high-water mark, and
every page it writes lies in `[old mark, new mark)`. Nothing is written twice.

**P2 — Nothing reachable from the live root is overwritten.** Immediate from P1
plus the reader's refusal to follow a pointer at or above the mark. This is the
`fresh` law of `RaftKV.Storage.Persist.Format`, and it is the reason the commit
sequence there is crash-safe when instantiated here.

**P3 — Reads through a root depend only on the pages below its mark.** This is
the `frame` law. Together with P1 and P2 it gives the theorem the crash-point
test was checking: after a crash at *any* point in a commit — any subset of the
new pages on the platter, arbitrary garbage everywhere else in the commit's
range — the old root reads back exactly the tree it read before, bit for bit.

**P4 — Search agrees with the contents.** `lookup` returns what was inserted;
insertion and deletion change the contents by exactly one binding and preserve
the ordering invariant that makes search work at all. This is the `correct` law,
and it is where a B-tree earns its name rather than its durability. Proved in
`RaftKV/Storage/BTreeContents.lean`.

The split is not an accident of what was easy. P1–P3 are statements about *where
bytes go*, and a bug in them silently destroys committed data. P4 is a statement
about *search*, and a bug in it is loud: the value you just wrote is not there.
-/

namespace RaftKV.BTree

/-! ## P1: allocation is monotone -/

private theorem nodup_snoc {α : Type} {l : List α} {x : α}
    (h : l.Nodup) (hx : x ∉ l) : (l ++ [x]).Nodup := by
  rw [List.nodup_append]
  refine ⟨h, ?_, ?_⟩
  · show List.Nodup [x]; simp
  · intro a ha b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    intro he; exact hx (he ▸ ha)

/-- An allocator that has only ever handed out pages at or above `base`. -/
structure Alloc.Grows (base : Nat) (a : Alloc) : Prop where
  /-- The mark never went down. -/
  le : base ≤ a.next
  /-- Every page written so far lies in `[base, next)`. -/
  mem : ∀ w ∈ a.writes, base ≤ w.1 ∧ w.1 < a.next
  /-- No page is written twice in one commit. -/
  nodup : (a.writes.map Prod.fst).Nodup

/-- Starting fresh at `base`. -/
theorem Alloc.grows_init (base : Nat) : Alloc.Grows base ⟨base, []⟩ :=
  ⟨Nat.le_refl _, by simp, by simp⟩

theorem Alloc.grows_push {base : Nat} {a : Alloc} {n : Node}
    (h : Alloc.Grows base a) : Alloc.Grows base (a.push n).2 := by
  refine ⟨Nat.le_succ_of_le h.le, ?_, ?_⟩
  · intro w hw
    simp only [Alloc.push, List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | hw
    · exact ⟨(h.mem w hw).1, Nat.lt_succ_of_lt (h.mem w hw).2⟩
    · subst hw; exact ⟨h.le, Nat.lt_succ_self _⟩
  · simp only [Alloc.push, List.map_append, List.map_cons, List.map_nil]
    refine nodup_snoc h.nodup ?_
    intro hx
    obtain ⟨w, hw, he⟩ := List.mem_map.mp hx
    exact absurd he (Nat.ne_of_lt (h.mem w hw).2)

theorem emit_grows {base : Nat} {a a' : Alloc} {n : Node} {r : Ins}
    {sp : Unit → Option (Node × Nat × Node)}
    (h : emit a n sp = some (r, a')) (hg : Alloc.Grows base a) : Alloc.Grows base a' := by
  unfold emit at h
  split at h
  · injection h with h; injection h with _ h; subst h
    exact Alloc.grows_push hg
  · split at h
    · exact absurd h (by simp)
    · rename_i l sep r' _
      split at h
      · injection h with h; injection h with _ h; subst h
        exact Alloc.grows_push (Alloc.grows_push hg)
      · exact absurd h (by simp)

/-- **P1 for insertion.** Every page the descent writes lies in `[base, next)`. -/
theorem insertAux_grows {t : Tree} {pages : Pages} {k : Nat} {v : ByteArray}
    {base : Nat} : ∀ (fuel p : Nat) {a a' : Alloc} {r : Ins},
    insertAux t pages k v fuel p a = some (r, a') → Alloc.Grows base a →
    Alloc.Grows base a'
  | 0, _, _, _, _, h, _ => by exact absurd h (by simp [insertAux])
  | fuel + 1, p, a, a', r, h, hg => by
      rw [insertAux] at h
      split at h
      · exact absurd h (by simp)
      · exact emit_grows h hg
      · dsimp only at h
        split at h
        · exact absurd h (by simp)
        · rename_i c _
          split at h
          · exact absurd h (by simp)
          · rename_i a2 hrec
            exact emit_grows h (insertAux_grows fuel c hrec hg)
          · rename_i a2 hrec
            exact emit_grows h (insertAux_grows fuel c hrec hg)

/-- **P1 for deletion.** -/
theorem eraseAux_grows {t : Tree} {pages : Pages} {k : Nat} {base : Nat} :
    ∀ (fuel p : Nat) {a a' : Alloc} {q : Nat},
    eraseAux t pages k fuel p a = some (q, a') → Alloc.Grows base a →
    Alloc.Grows base a'
  | 0, _, _, _, _, h, _ => by exact absurd h (by simp [eraseAux])
  | fuel + 1, p, a, a', q, h, hg => by
      rw [eraseAux] at h
      split at h
      · exact absurd h (by simp)
      · injection h with h; injection h with _ h; subst h
        exact Alloc.grows_push hg
      · dsimp only at h
        split at h
        · exact absurd h (by simp)
        · rename_i c _
          split at h
          · exact absurd h (by simp)
          · rename_i a2 hrec
            injection h with h; injection h with _ h; subst h
            exact Alloc.grows_push (eraseAux_grows fuel c hrec hg)

/-- The mark only ever grows, and pushing bumps it by one. -/
theorem Alloc.push_next {a : Alloc} {n : Node} : (a.push n).2.next = a.next + 1 := rfl

/-- The page a push hands out is the old mark. -/
theorem Alloc.push_page {a : Alloc} {n : Node} : (a.push n).1 = a.next := rfl

end RaftKV.BTree

namespace RaftKV.BTree

/--
**P1, at the top.** An insert never lowers the high-water mark, writes only
pages in `[old mark, new mark)`, and writes no page twice.
-/
theorem insert_grows {t t' : Tree} {pages : Pages} {k : Nat} {v : ByteArray}
    {ws : List (Nat × Node)} (h : t.insert pages k v = some (t', ws)) :
    t.next ≤ t'.next ∧ (∀ w ∈ ws, t.next ≤ w.1 ∧ w.1 < t'.next) ∧ (ws.map Prod.fst).Nodup := by
  unfold Tree.insert at h
  split at h
  · -- empty tree: one fresh leaf
    dsimp only at h
    split at h
    · injection h with h; injection h with h1 h2
      subst h1; subst h2
      have hg := Alloc.grows_push (n := Node.leaf #[(k, v)]) (Alloc.grows_init t.next)
      exact ⟨hg.le, hg.mem, hg.nodup⟩
    · exact absurd h (by simp)
  · rename_i r _
    split at h
    · exact absurd h (by simp)
    · rename_i q a hrec
      injection h with h; injection h with h1 h2
      subst h1; subst h2
      have hg := insertAux_grows (base := t.next) _ r hrec (Alloc.grows_init _)
      exact ⟨hg.le, hg.mem, hg.nodup⟩
    · rename_i lq sep rq a hrec
      injection h with h; injection h with h1 h2
      subst h1; subst h2
      have hg := Alloc.grows_push (n := Node.branch #[sep] #[lq, rq])
        (insertAux_grows (base := t.next) _ r hrec (Alloc.grows_init _))
      exact ⟨hg.le, hg.mem, hg.nodup⟩

/-- **P1 for deletion.** -/
theorem erase_grows {t t' : Tree} {pages : Pages} {k : Nat}
    {ws : List (Nat × Node)} (h : t.erase pages k = some (t', ws)) :
    t.next ≤ t'.next ∧ (∀ w ∈ ws, t.next ≤ w.1 ∧ w.1 < t'.next) ∧ (ws.map Prod.fst).Nodup := by
  unfold Tree.erase at h
  split at h
  · injection h with h; injection h with h1 h2
    subst h1; subst h2
    exact ⟨Nat.le_refl _, by simp, by simp⟩
  · rename_i r _
    split at h
    · exact absurd h (by simp)
    · rename_i q a hrec
      injection h with h; injection h with h1 h2
      subst h1; subst h2
      have hg := eraseAux_grows (base := t.next) _ r hrec (Alloc.grows_init _)
      exact ⟨hg.le, hg.mem, hg.nodup⟩

/-! ## P3: reads depend only on the pages below the mark -/

theorem get_congr {t : Tree} {f g : Pages} {p : Nat}
    (h : ∀ q, q < t.next → f q = g q) : t.get f p = t.get g p := by
  unfold Tree.get
  split
  · exact h p (by assumption)
  · rfl

theorem lookupAux_congr {t : Tree} {f g : Pages} {k : Nat}
    (h : ∀ q, q < t.next → f q = g q) :
    ∀ (fuel p : Nat), lookupAux t f k fuel p = lookupAux t g k fuel p
  | 0, _ => rfl
  | fuel + 1, p => by
      rw [lookupAux, lookupAux, get_congr h]
      split
      · rfl
      · rfl
      · split
        · rfl
        · exact lookupAux_congr h fuel _

theorem toListAux_congr {t : Tree} {f g : Pages}
    (h : ∀ q, q < t.next → f q = g q) :
    ∀ (fuel p : Nat), toListAux t f fuel p = toListAux t g fuel p
  | 0, _ => rfl
  | fuel + 1, p => by
      rw [toListAux, toListAux, get_congr h]
      split
      · rfl
      · rfl
      · rename_i children _
        refine congrArg List.flatten ?_
        refine List.map_congr_left ?_
        exact fun c _ => toListAux_congr h fuel c

/--
**P3.** Everything a root cell can see lies below its own high-water mark, so
two page images agreeing there are indistinguishable through it.
-/
theorem lookup_frame {t : Tree} {f g : Pages} {k : Nat}
    (h : ∀ q, q < t.next → f q = g q) : t.lookup f k = t.lookup g k := by
  unfold Tree.lookup
  split
  · rfl
  · exact lookupAux_congr h _ _

theorem toList_frame {t : Tree} {f g : Pages}
    (h : ∀ q, q < t.next → f q = g q) : t.toList f = t.toList g := by
  unfold Tree.toList
  split
  · rfl
  · exact toListAux_congr h _ _

end RaftKV.BTree

namespace RaftKV.BTree

/-! ## P2: what a crash can leave behind, and why it does not matter -/

/-- Apply a commit's page writes to an image. -/
def patch (f : Pages) (ws : List (Nat × Node)) : Pages :=
  ws.foldl (fun g w => fun q => if q = w.1 then some w.2 else g q) f

theorem patch_below {f : Pages} {b : Nat} :
    ∀ (ws : List (Nat × Node)), (∀ w ∈ ws, b ≤ w.1) → ∀ q, q < b → patch f ws q = f q
  | [], _, _, _ => rfl
  | w :: ws, hb, q, hq => by
      have hrest : ∀ x ∈ ws, b ≤ x.1 := fun x hx => hb x (List.mem_cons_of_mem _ hx)
      have : patch f (w :: ws) q
          = patch (fun r => if r = w.1 then some w.2 else f r) ws q := rfl
      rw [this, patch_below ws hrest q hq]
      exact if_neg (fun he => absurd (he ▸ hq) (Nat.not_lt.mpr (hb w (List.mem_cons_self ..))))

/--
**The crash theorem for the B-tree.**

Suppose a commit was in progress: `insert` produced a new root cell and a list of
pages to write. Then for *any* image `g` that agrees with the pre-commit image
below the old high-water mark — which is every image a crash can leave, since
the commit only writes at or above that mark, and the pages it was allocating
may hold anything at all — and for *any* subset of the commit's writes having
reached the platter, in any order, the old root cell reads back exactly the tree
it read before. Every key, and the whole ordered scan.

This is what the crash-point test in `Test/BTree.lean` was checking one prefix
at a time, now proved for all of them at once, and for arbitrary garbage rather
than the one byte pattern the test used.
-/
theorem insert_crash_safe {t t' : Tree} {f : Pages} {k : Nat} {v : ByteArray}
    {ws : List (Nat × Node)} (hins : t.insert f k v = some (t', ws))
    (g : Pages) (hg : ∀ q, q < t.next → g q = f q)
    (ws' : List (Nat × Node)) (hsub : ∀ w ∈ ws', w ∈ ws) :
    (∀ k', t.lookup (patch g ws') k' = t.lookup f k') ∧ t.toList (patch g ws') = t.toList f := by
  have hfresh : ∀ w ∈ ws', t.next ≤ w.1 := fun w hw => ((insert_grows hins).2.1 w (hsub w hw)).1
  have hagree : ∀ q, q < t.next → patch g ws' q = f q := fun q hq => by
    rw [patch_below ws' hfresh q hq]; exact hg q hq
  exact ⟨fun k' => lookup_frame hagree, toList_frame hagree⟩

/-- The same, for a delete. -/
theorem erase_crash_safe {t t' : Tree} {f : Pages} {k : Nat}
    {ws : List (Nat × Node)} (her : t.erase f k = some (t', ws))
    (g : Pages) (hg : ∀ q, q < t.next → g q = f q)
    (ws' : List (Nat × Node)) (hsub : ∀ w ∈ ws', w ∈ ws) :
    (∀ k', t.lookup (patch g ws') k' = t.lookup f k') ∧ t.toList (patch g ws') = t.toList f := by
  have hfresh : ∀ w ∈ ws', t.next ≤ w.1 := fun w hw => ((erase_grows her).2.1 w (hsub w hw)).1
  have hagree : ∀ q, q < t.next → patch g ws' q = f q := fun q hq => by
    rw [patch_below ws' hfresh q hq]; exact hg q hq
  exact ⟨fun k' => lookup_frame hagree, toList_frame hagree⟩

end RaftKV.BTree

namespace RaftKV.BTree

/-!
## How an allocator grows during one update

`Alloc.Grows` says where a whole commit's pages live. Proving the *contents* of
the new tree needs the finer statement: each step only appends, and only at or
above the mark it started from. That is what lets a subtree written early in the
descent keep its meaning as the descent continues past it.
-/

/-- `a'` is `a` plus writes at or above `a`'s mark. -/
structure Alloc.Extends (a a' : Alloc) : Prop where
  /-- The mark did not go down. -/
  le : a.next ≤ a'.next
  /-- The new writes are appended, and all at or above the old mark. -/
  ext : ∃ e, a'.writes = a.writes ++ e ∧ ∀ w ∈ e, a.next ≤ w.1

theorem Alloc.extends_refl (a : Alloc) : Alloc.Extends a a :=
  ⟨Nat.le_refl _, [], by simp, by simp⟩

theorem Alloc.extends_trans {a b c : Alloc}
    (h1 : Alloc.Extends a b) (h2 : Alloc.Extends b c) : Alloc.Extends a c := by
  obtain ⟨e1, he1, hb1⟩ := h1.ext
  obtain ⟨e2, he2, hb2⟩ := h2.ext
  refine ⟨Nat.le_trans h1.le h2.le, e1 ++ e2, by rw [he2, he1, List.append_assoc], ?_⟩
  intro w hw
  rcases List.mem_append.mp hw with h | h
  · exact hb1 w h
  · exact Nat.le_trans h1.le (hb2 w h)

theorem Alloc.extends_push {a : Alloc} {n : Node} : Alloc.Extends a (a.push n).2 :=
  ⟨Nat.le_succ _, [(a.next, n)], rfl, by intro w hw; simp at hw; subst hw; exact Nat.le_refl _⟩

theorem emit_extends {a a' : Alloc} {n : Node} {r : Ins}
    {sp : Unit → Option (Node × Nat × Node)}
    (h : emit a n sp = some (r, a')) : Alloc.Extends a a' := by
  unfold emit at h
  split at h
  · injection h with h; injection h with _ h; subst h
    exact Alloc.extends_push
  · split at h
    · exact absurd h (by simp)
    · split at h
      · injection h with h; injection h with _ h; subst h
        exact Alloc.extends_trans Alloc.extends_push Alloc.extends_push
      · exact absurd h (by simp)

theorem insertAux_extends {t : Tree} {pages : Pages} {k : Nat} {v : ByteArray} :
    ∀ (fuel p : Nat) {a a' : Alloc} {r : Ins},
    insertAux t pages k v fuel p a = some (r, a') → Alloc.Extends a a'
  | 0, _, _, _, _, h => by exact absurd h (by simp [insertAux])
  | fuel + 1, p, a, a', r, h => by
      rw [insertAux] at h
      split at h
      · exact absurd h (by simp)
      · exact emit_extends h
      · dsimp only at h
        split at h
        · exact absurd h (by simp)
        · rename_i c _
          split at h
          · exact absurd h (by simp)
          · rename_i a2 hrec
            exact Alloc.extends_trans (insertAux_extends fuel c hrec) (emit_extends h)
          · rename_i a2 hrec
            exact Alloc.extends_trans (insertAux_extends fuel c hrec) (emit_extends h)

theorem eraseAux_extends {t : Tree} {pages : Pages} {k : Nat} :
    ∀ (fuel p : Nat) {a a' : Alloc} {q : Nat},
    eraseAux t pages k fuel p a = some (q, a') → Alloc.Extends a a'
  | 0, _, _, _, _, h => by exact absurd h (by simp [eraseAux])
  | fuel + 1, p, a, a', q, h => by
      rw [eraseAux] at h
      split at h
      · exact absurd h (by simp)
      · injection h with h; injection h with _ h; subst h
        exact Alloc.extends_push
      · dsimp only at h
        split at h
        · exact absurd h (by simp)
        · rename_i c _
          split at h
          · exact absurd h (by simp)
          · rename_i a2 hrec
            injection h with h; injection h with _ h; subst h
            exact Alloc.extends_trans (eraseAux_extends fuel c hrec) Alloc.extends_push

/-! ### Patching, step by step -/

theorem patch_append (f : Pages) (ws e : List (Nat × Node)) :
    patch f (ws ++ e) = patch (patch f ws) e := List.foldl_append ..

/-- The image after `a'` agrees with the image after `a` on everything below `a`'s mark. -/
theorem patch_extends {f : Pages} {a a' : Alloc} (h : Alloc.Extends a a') :
    ∀ q, q < a.next → patch f a'.writes q = patch f a.writes q := by
  obtain ⟨e, he, hb⟩ := h.ext
  intro q hq
  rw [he, patch_append, patch_below e hb q hq]

/-- Writing a page leaves every other page alone. -/
theorem patch_push_ne (f : Pages) (a : Alloc) (n : Node) {q : Nat} (hq : q ≠ a.next) :
    patch f (a.push n).2.writes q = patch f a.writes q := by
  show patch f (a.writes ++ [(a.next, n)]) q = _
  rw [patch_append]
  show (if q = a.next then some n else _) = _
  rw [if_neg hq]

/-- A page just written reads back as what was written. -/
theorem patch_push (f : Pages) (a : Alloc) (n : Node) :
    patch f (a.push n).2.writes a.next = some n := by
  show patch f (a.writes ++ [(a.next, n)]) a.next = some n
  rw [patch_append]
  show (if a.next = a.next then some n else _) = some n
  rw [if_pos rfl]

/-- Of two pages written in succession, the first still reads back. -/
theorem patch_push_two (f : Pages) (a : Alloc) (n1 n2 : Node) :
    patch f (((a.push n1).2).push n2).2.writes a.next = some n1 := by
  rw [patch_push_ne f (a.push n1).2 n2 (by
    show a.next ≠ a.next + 1
    omega)]
  exact patch_push f a n1

end RaftKV.BTree
