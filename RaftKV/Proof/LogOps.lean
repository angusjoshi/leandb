import RaftKV.Proof.VotesChar

/-!
# How `appendFrom` reshapes a log

The structural facts about splicing an `AppendEntries` payload into a follower's
log. These are the groundwork for Log Matching: they say precisely which parts
of the log the splice can and cannot touch, and what the spliced region ends up
containing.

Every lemma carries the bound `startIdx ≤ lastIndex lg + 1` — the splice must
start no further than one past the end. That is not an artificial hypothesis:
`handleAppendEntries` only calls `appendFrom` with `startIdx = prevIdx + 1`
after checking that the log actually reaches `prevIdx`, and
`appendFrom_bound_step` below shows the bound is re-established at each
recursive call.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ : Type} [LogStore σ] [LawfulLogStore σ]

/-- After splicing one entry at `startIdx`, the log reaches exactly `startIdx`. -/
theorem appendFrom_one_lastIndex (lg : σ) (startIdx : Nat)
    (hb : startIdx ≤ LogStore.lastIndex lg + 1) (hb1 : 1 ≤ startIdx) (e : Entry) :
    LogStore.lastIndex
        (if (LogStore.get lg startIdx).isSome then
          LogStore.append (LogStore.truncFrom lg startIdx) e
         else LogStore.append lg e) = startIdx := by
  split
  · rename_i h
    have hle : startIdx ≤ LogStore.lastIndex lg :=
      ((LogStore.get_isSome_iff lg startIdx).mp h).2
    rw [LogStore.lastIndex_append, LogStore.lastIndex_truncFrom_of_le _ _ hle]
    omega
  · rename_i h
    have hnone : ¬(1 ≤ startIdx ∧ startIdx ≤ LogStore.lastIndex lg) := by
      intro hc; exact h ((LogStore.get_isSome_iff lg startIdx).mpr hc)
    rw [LogStore.lastIndex_append]
    omega

/--
**Splicing never disturbs the log below the splice point.**

This is what makes `AppendEntries` idempotent under duplication and reordering:
a message that repeats work already done cannot corrupt earlier entries.
-/
theorem appendFrom_get_of_lt : ∀ (es : List Entry) (lg : σ) (startIdx i : Nat),
    startIdx ≤ LogStore.lastIndex lg + 1 → i < startIdx →
    LogStore.get (appendFrom lg startIdx es) i = LogStore.get lg i := by
  intro es
  induction es with
  | nil => intro lg startIdx i _ _; rfl
  | cons e es ih =>
    intro lg startIdx i hb hi
    rw [appendFrom]
    cases hg : LogStore.get lg startIdx with
    | some existing =>
        dsimp only
        have hle : startIdx ≤ LogStore.lastIndex lg :=
          ((LogStore.get_isSome_iff lg startIdx).mp (by rw [hg]; rfl)).2
        by_cases hterm : existing.term == e.term
        · rw [if_pos hterm]
          exact ih lg (startIdx + 1) i (by omega) (by omega)
        · rw [if_neg hterm]
          have hlast : LogStore.lastIndex (LogStore.truncFrom lg startIdx) = startIdx - 1 :=
            LogStore.lastIndex_truncFrom_of_le _ _ hle
          have h1 : 1 ≤ startIdx :=
            ((LogStore.get_isSome_iff lg startIdx).mp (by rw [hg]; rfl)).1
          have hb' : startIdx + 1
              ≤ LogStore.lastIndex (LogStore.append (LogStore.truncFrom lg startIdx) e) + 1 := by
            rw [LogStore.lastIndex_append, hlast]; omega
          rw [ih _ (startIdx + 1) i hb' (by omega)]
          rw [LogStore.get_append_of_le _ _ _ (by rw [hlast]; omega)]
          exact LogStore.get_truncFrom_of_lt lg startIdx i hi
    | none =>
        dsimp only
        have hnot : ¬(1 ≤ startIdx ∧ startIdx ≤ LogStore.lastIndex lg) := by
          intro hc
          have := (LogStore.get_isSome_iff lg startIdx).mpr hc
          rw [hg] at this; exact Bool.noConfusion this
        have hb' : startIdx + 1 ≤ LogStore.lastIndex (LogStore.append lg e) + 1 := by
          rw [LogStore.lastIndex_append]; omega
        rw [ih _ (startIdx + 1) i hb' (by omega)]
        exact LogStore.get_append_of_le _ _ _ (by omega)

/-- Splicing only ever extends the log's reach to cover what it wrote. -/
theorem appendFrom_lastIndex_ge : ∀ (es : List Entry) (lg : σ) (startIdx : Nat),
    startIdx ≤ LogStore.lastIndex lg + 1 →
    LogStore.lastIndex (appendFrom lg startIdx es) + 1 ≥ startIdx + es.length := by
  intro es
  induction es with
  | nil => intro lg startIdx hb; show LogStore.lastIndex lg + 1 ≥ startIdx + 0; omega
  | cons e es ih =>
    intro lg startIdx hb
    rw [appendFrom]
    cases hg : LogStore.get lg startIdx with
    | some existing =>
        dsimp only
        have hle : startIdx ≤ LogStore.lastIndex lg :=
          ((LogStore.get_isSome_iff lg startIdx).mp (by rw [hg]; rfl)).2
        by_cases hterm : existing.term == e.term
        · rw [if_pos hterm]
          have := ih lg (startIdx + 1) (by omega)
          simp only [List.length_cons]; omega
        · rw [if_neg hterm]
          have hlast : LogStore.lastIndex (LogStore.truncFrom lg startIdx) = startIdx - 1 :=
            LogStore.lastIndex_truncFrom_of_le _ _ hle
          have h1 : 1 ≤ startIdx := by
            have := ((LogStore.get_isSome_iff lg startIdx).mp (by rw [hg]; rfl)).1; omega
          have hb' : startIdx + 1
              ≤ LogStore.lastIndex (LogStore.append (LogStore.truncFrom lg startIdx) e) + 1 := by
            rw [LogStore.lastIndex_append, hlast]; omega
          have := ih _ (startIdx + 1) hb'
          simp only [List.length_cons]; omega
    | none =>
        dsimp only
        have hb' : startIdx + 1 ≤ LogStore.lastIndex (LogStore.append lg e) + 1 := by
          rw [LogStore.lastIndex_append]; omega
        have := ih _ (startIdx + 1) hb'
        simp only [List.length_cons]; omega

/--
**Splicing preserves any per-entry property shared by the log and the payload.**

The workhorse for `LogFromCreated`. Whatever ends up in the log after a splice
came from one of two places: it was already there (the matching-term branch
keeps existing entries), or it is one of the payload's entries written at its
intended index. So a property `P` holding of both survives the splice.
-/
theorem appendFrom_mem (P : Nat → Entry → Prop) :
    ∀ (es : List Entry) (lg : σ) (startIdx : Nat),
      startIdx ≤ LogStore.lastIndex lg + 1 → 1 ≤ startIdx →
      (∀ k e, LogStore.get lg k = some e → P k e) →
      (∀ n e, es[n]? = some e → P (startIdx + n) e) →
      ∀ k e, LogStore.get (appendFrom lg startIdx es) k = some e → P k e := by
  intro es
  induction es with
  | nil => intro lg startIdx _ _ hlog _ k e h; exact hlog k e h
  | cons a es ih =>
    intro lg startIdx hb h1 hlog hes k e h
    rw [appendFrom] at h
    cases hg : LogStore.get lg startIdx with
    | some existing =>
        rw [hg] at h
        dsimp only at h
        have hle : startIdx ≤ LogStore.lastIndex lg :=
          ((LogStore.get_isSome_iff lg startIdx).mp (by rw [hg]; rfl)).2
        by_cases hterm : existing.term == a.term
        · rw [if_pos hterm] at h
          exact ih lg (startIdx + 1) (by omega) (by omega) hlog
            (fun n e' he' => by
              have := hes (n + 1) e' (by simpa using he')
              rwa [show startIdx + 1 + n = startIdx + (n + 1) by omega]) k e h
        · rw [if_neg hterm] at h
          have hlast : LogStore.lastIndex (LogStore.truncFrom lg startIdx) = startIdx - 1 :=
            LogStore.lastIndex_truncFrom_of_le _ _ hle
          refine ih _ (startIdx + 1) (by rw [LogStore.lastIndex_append, hlast]; omega)
            (by omega) ?_ (fun n e' he' => by
              have := hes (n + 1) e' (by simpa using he')
              rwa [show startIdx + 1 + n = startIdx + (n + 1) by omega]) k e h
          -- the spliced log: old entries below the cut, plus `a` at `startIdx`
          intro k' e' hk'
          rw [LogStore.get_append, hlast] at hk'
          by_cases hcut : k' = startIdx - 1 + 1
          · rw [if_pos hcut] at hk'
            have : e' = a := Option.some.inj hk'.symm
            subst this
            have := hes 0 e' (by simp)
            rwa [show startIdx + 0 = k' by omega] at this
          · rw [if_neg hcut, LogStore.get_truncFrom] at hk'
            split at hk'
            · exact hlog k' e' hk'
            · exact absurd hk' (by simp)
    | none =>
        rw [hg] at h
        dsimp only at h
        have hnot : LogStore.lastIndex lg < startIdx := by
          rcases Nat.lt_or_ge (LogStore.lastIndex lg) startIdx with hc | hc
          · exact hc
          · exfalso
            have := (LogStore.get_isSome_iff lg startIdx).mpr ⟨h1, hc⟩
            rw [hg] at this; exact Bool.noConfusion this
        have hlast : LogStore.lastIndex lg = startIdx - 1 := by omega
        refine ih _ (startIdx + 1) (by rw [LogStore.lastIndex_append]; omega) (by omega) ?_
          (fun n e' he' => by
            have := hes (n + 1) e' (by simpa using he')
            rwa [show startIdx + 1 + n = startIdx + (n + 1) by omega]) k e h
        intro k' e' hk'
        rw [LogStore.get_append, hlast] at hk'
        by_cases hcut : k' = startIdx - 1 + 1
        · rw [if_pos hcut] at hk'
          have : e' = a := Option.some.inj hk'.symm
          subst this
          have := hes 0 e' (by simp)
          rwa [show startIdx + 0 = k' by omega] at this
        · rw [if_neg hcut] at hk'
          exact hlog k' e' hk'

/--
**The term at each spliced index is the payload's term there.**

Note this holds even in the branch that *keeps* an existing entry: that branch
fires only when the terms already agree, so the term at the index is the
payload's either way.
-/
theorem appendFrom_termAt : ∀ (es : List Entry) (lg : σ) (startIdx n : Nat) (e : Entry),
    startIdx ≤ LogStore.lastIndex lg + 1 → 1 ≤ startIdx → es[n]? = some e →
    LogStore.termAt (appendFrom lg startIdx es) (startIdx + n) = some e.term := by
  intro es
  induction es with
  | nil => intro lg startIdx n e _ _ hn; simp at hn
  | cons a es ih =>
    intro lg startIdx n e hb h1 hn
    rw [appendFrom]
    cases hg : LogStore.get lg startIdx with
    | some existing =>
        dsimp only
        have hle : startIdx ≤ LogStore.lastIndex lg :=
          ((LogStore.get_isSome_iff lg startIdx).mp (by rw [hg]; rfl)).2
        by_cases hterm : existing.term == a.term
        · rw [if_pos hterm]
          cases n with
          | zero =>
              have hea : a = e := by simpa using hn
              unfold LogStore.termAt
              simp only [Nat.add_zero]
              rw [appendFrom_get_of_lt es lg (startIdx + 1) startIdx (by omega) (by omega), hg]
              have hte : existing.term = a.term := by simpa using hterm
              simp [hte, hea]
          | succ m =>
              have := ih lg (startIdx + 1) m e (by omega) (by omega) (by simpa using hn)
              rwa [show startIdx + 1 + m = startIdx + (m + 1) by omega] at this
        · rw [if_neg hterm]
          have hlast : LogStore.lastIndex (LogStore.truncFrom lg startIdx) = startIdx - 1 :=
            LogStore.lastIndex_truncFrom_of_le _ _ hle
          have hb' : startIdx + 1
              ≤ LogStore.lastIndex (LogStore.append (LogStore.truncFrom lg startIdx) a) + 1 := by
            rw [LogStore.lastIndex_append, hlast]; omega
          cases n with
          | zero =>
              have hea : a = e := by simpa using hn
              unfold LogStore.termAt
              simp only [Nat.add_zero]
              rw [appendFrom_get_of_lt es _ (startIdx + 1) startIdx hb' (by omega)]
              rw [LogStore.get_append, hlast, if_pos (by omega)]
              simp [hea]
          | succ m =>
              have := ih _ (startIdx + 1) m e hb' (by omega) (by simpa using hn)
              rwa [show startIdx + 1 + m = startIdx + (m + 1) by omega] at this
    | none =>
        dsimp only
        have hnot : LogStore.lastIndex lg < startIdx := by
          rcases Nat.lt_or_ge (LogStore.lastIndex lg) startIdx with hc | hc
          · exact hc
          · exfalso
            have := (LogStore.get_isSome_iff lg startIdx).mpr ⟨h1, hc⟩
            rw [hg] at this; exact Bool.noConfusion this
        have hlast : LogStore.lastIndex lg = startIdx - 1 := by omega
        have hb' : startIdx + 1 ≤ LogStore.lastIndex (LogStore.append lg a) + 1 := by
          rw [LogStore.lastIndex_append]; omega
        cases n with
        | zero =>
            have hea : a = e := by simpa using hn
            unfold LogStore.termAt
            simp only [Nat.add_zero]
            rw [appendFrom_get_of_lt es _ (startIdx + 1) startIdx hb' (by omega)]
            rw [LogStore.get_append, hlast, if_pos (by omega)]
            simp [hea]
        | succ m =>
            have := ih _ (startIdx + 1) m e hb' (by omega) (by simpa using hn)
            rwa [show startIdx + 1 + m = startIdx + (m + 1) by omega] at this

/-- Beyond the spliced range the log is either untouched or has ended. -/
theorem appendFrom_get_above : ∀ (es : List Entry) (lg : σ) (startIdx k : Nat),
    startIdx ≤ LogStore.lastIndex lg + 1 → 1 ≤ startIdx → startIdx + es.length ≤ k →
    LogStore.get (appendFrom lg startIdx es) k = LogStore.get lg k
      ∨ LogStore.get (appendFrom lg startIdx es) k = none := by
  intro es
  induction es with
  | nil => intro lg startIdx k _ _ _; exact Or.inl rfl
  | cons a es ih =>
    intro lg startIdx k hb h1 hk
    rw [appendFrom]
    cases hg : LogStore.get lg startIdx with
    | some existing =>
        dsimp only
        have hle : startIdx ≤ LogStore.lastIndex lg :=
          ((LogStore.get_isSome_iff lg startIdx).mp (by rw [hg]; rfl)).2
        by_cases hterm : existing.term == a.term
        · rw [if_pos hterm]
          exact ih lg (startIdx + 1) k (by omega) (by omega) (by simp at hk ⊢; omega)
        · rw [if_neg hterm]
          have hlast : LogStore.lastIndex (LogStore.truncFrom lg startIdx) = startIdx - 1 :=
            LogStore.lastIndex_truncFrom_of_le _ _ hle
          have hb' : startIdx + 1
              ≤ LogStore.lastIndex (LogStore.append (LogStore.truncFrom lg startIdx) a) + 1 := by
            rw [LogStore.lastIndex_append, hlast]; omega
          rcases ih _ (startIdx + 1) k hb' (by omega) (by simp at hk ⊢; omega) with h | h
          · right
            rw [h, LogStore.get_append, hlast, if_neg (by simp at hk; omega),
              LogStore.get_truncFrom, if_neg (by simp at hk; omega)]
          · exact Or.inr h
    | none =>
        dsimp only
        have hnot : LogStore.lastIndex lg < startIdx := by
          rcases Nat.lt_or_ge (LogStore.lastIndex lg) startIdx with hc | hc
          · exact hc
          · exfalso
            have := (LogStore.get_isSome_iff lg startIdx).mpr ⟨h1, hc⟩
            rw [hg] at this; exact Bool.noConfusion this
        have hb' : startIdx + 1 ≤ LogStore.lastIndex (LogStore.append lg a) + 1 := by
          rw [LogStore.lastIndex_append]; omega
        rcases ih _ (startIdx + 1) k hb' (by omega) (by simp at hk ⊢; omega) with h | h
        · right
          rw [h, LogStore.get_append, if_neg (by simp at hk; omega)]
          rcases Option.eq_none_or_eq_some (LogStore.get lg k) with hq | ⟨v, hq⟩
          · exact hq
          · exfalso
            have := ((LogStore.get_isSome_iff lg k).mp (by rw [hq]; rfl)).2
            simp at hk; omega
        · exact Or.inr h

/-- A splice never leaves the log longer than the old log or the spliced range. -/
theorem appendFrom_lastIndex_le : ∀ (es : List Entry) (lg : σ) (startIdx : Nat),
    startIdx ≤ LogStore.lastIndex lg + 1 → 1 ≤ startIdx →
    LogStore.lastIndex (appendFrom lg startIdx es)
      ≤ max (LogStore.lastIndex lg) (startIdx + es.length - 1) := by
  intro es
  induction es with
  | nil =>
      intro lg startIdx _ _
      show LogStore.lastIndex lg ≤ _
      exact Nat.le_max_left _ _
  | cons a es ih =>
    intro lg startIdx hb h1
    rw [appendFrom]
    cases hg : LogStore.get lg startIdx with
    | some existing =>
        dsimp only
        have hle : startIdx ≤ LogStore.lastIndex lg :=
          ((LogStore.get_isSome_iff lg startIdx).mp (by rw [hg]; rfl)).2
        by_cases hterm : existing.term == a.term
        · rw [if_pos hterm]
          have := ih lg (startIdx + 1) (by omega) (by omega)
          simp only [List.length_cons]; omega
        · rw [if_neg hterm]
          have hlast : LogStore.lastIndex (LogStore.truncFrom lg startIdx) = startIdx - 1 :=
            LogStore.lastIndex_truncFrom_of_le _ _ hle
          have hlg' : LogStore.lastIndex (LogStore.append (LogStore.truncFrom lg startIdx) a)
              = startIdx := by rw [LogStore.lastIndex_append, hlast]; omega
          have := ih (LogStore.append (LogStore.truncFrom lg startIdx) a) (startIdx + 1)
            (by rw [hlg']; omega) (by omega)
          rw [hlg'] at this
          simp only [List.length_cons]; omega
    | none =>
        dsimp only
        have hnot : LogStore.lastIndex lg < startIdx := by
          rcases Nat.lt_or_ge (LogStore.lastIndex lg) startIdx with hc | hc
          · exact hc
          · exfalso
            have := (LogStore.get_isSome_iff lg startIdx).mpr ⟨h1, hc⟩
            rw [hg] at this; exact Bool.noConfusion this
        have hlg' : LogStore.lastIndex (LogStore.append lg a) = startIdx := by
          rw [LogStore.lastIndex_append]; omega
        have := ih (LogStore.append lg a) (startIdx + 1) (by rw [hlg']; omega) (by omega)
        rw [hlg'] at this
        simp only [List.length_cons]; omega

/--
**Reaching beyond the spliced range means the splice changed nothing.**

If the log still has an entry past everything the payload covers, no conflict
was found, so every step took the keep-existing branch and the log is untouched.
-/
theorem appendFrom_above_unchanged : ∀ (es : List Entry) (lg : σ) (startIdx k : Nat),
    startIdx ≤ LogStore.lastIndex lg + 1 → 1 ≤ startIdx → startIdx + es.length ≤ k →
    (LogStore.get (appendFrom lg startIdx es) k).isSome →
    ∀ m, LogStore.get (appendFrom lg startIdx es) m = LogStore.get lg m := by
  intro es
  induction es with
  | nil => intro lg startIdx k _ _ _ _ m; rfl
  | cons a es ih =>
    intro lg startIdx k hb h1 hk hsome m
    rw [appendFrom] at hsome ⊢
    cases hg : LogStore.get lg startIdx with
    | some existing =>
        rw [hg] at hsome
        dsimp only at hsome ⊢
        have hle : startIdx ≤ LogStore.lastIndex lg :=
          ((LogStore.get_isSome_iff lg startIdx).mp (by rw [hg]; rfl)).2
        by_cases hterm : existing.term == a.term
        · rw [if_pos hterm] at hsome ⊢
          exact ih lg (startIdx + 1) k (by omega) (by omega) (by simp at hk ⊢; omega) hsome m
        · exfalso
          rw [if_neg hterm] at hsome
          have hlast : LogStore.lastIndex (LogStore.truncFrom lg startIdx) = startIdx - 1 :=
            LogStore.lastIndex_truncFrom_of_le _ _ hle
          have hlg' : LogStore.lastIndex (LogStore.append (LogStore.truncFrom lg startIdx) a)
              = startIdx := by rw [LogStore.lastIndex_append, hlast]; omega
          have hb2 := appendFrom_lastIndex_le es
            (LogStore.append (LogStore.truncFrom lg startIdx) a) (startIdx + 1)
            (by rw [hlg']; omega) (by omega)
          rw [hlg'] at hb2
          have := ((LogStore.get_isSome_iff _ k).mp hsome).2
          simp at hk
          omega
    | none =>
        rw [hg] at hsome
        dsimp only at hsome ⊢
        exfalso
        have hnot : LogStore.lastIndex lg < startIdx := by
          rcases Nat.lt_or_ge (LogStore.lastIndex lg) startIdx with hc | hc
          · exact hc
          · exfalso
            have := (LogStore.get_isSome_iff lg startIdx).mpr ⟨h1, hc⟩
            rw [hg] at this; exact Bool.noConfusion this
        have hlg' : LogStore.lastIndex (LogStore.append lg a) = startIdx := by
          rw [LogStore.lastIndex_append]; omega
        have hb2 := appendFrom_lastIndex_le es (LogStore.append lg a) (startIdx + 1)
          (by rw [hlg']; omega) (by omega)
        rw [hlg'] at hb2
        have := ((LogStore.get_isSome_iff _ k).mp hsome).2
        simp at hk
        omega

/-! ## How a step can change the log -/

section StepLog

variable {κ : Type} [KVStore κ]

/-- The follower side of replication either leaves the log alone or splices. -/
theorem handleAppendEntries_log {s : NodeState σ κ}
    {src term leaderId prevIdx prevTerm : Nat} {es : List Entry} {lc : Nat} :
    (handleAppendEntries s src term leaderId prevIdx prevTerm es lc).1.log = s.log
      ∨ ((handleAppendEntries s src term leaderId prevIdx prevTerm es lc).1.log
            = appendFrom s.log (prevIdx + 1) es
          ∧ prevIdx ≤ LogStore.lastIndex s.log
          ∧ (prevIdx ≠ 0 → LogStore.termAt s.log prevIdx = some prevTerm)
          ∧ (handleAppendEntries s src term leaderId prevIdx prevTerm es lc).1.role
              = Role.follower
          ∧ s.currentTerm ≤ term) := by
  rw [handleAppendEntries]
  split
  · exact Or.inl rfl
  · dsimp only
    have hmsd : (maybeStepDown s term (some leaderId)).1.log = s.log := by
      rw [maybeStepDown]; split <;> rfl
    split
    · exact Or.inl (by simpa using hmsd)
    · rename_i hcons
      right
      have hc : ¬prevIdx = 0 → LogStore.termAt s.log prevIdx = some prevTerm := by
        simpa [hmsd] using hcons
      refine ⟨by simp [hmsd], ?_, hc, by simp, by omega⟩
      by_cases h0 : prevIdx = 0
      · omega
      · have hg := hc h0
        have hsome : (LogStore.get s.log prevIdx).isSome := by
          cases hq : LogStore.get s.log prevIdx with
          | none => unfold LogStore.termAt at hg; rw [hq] at hg; simp at hg
          | some _ => rfl
        exact ((LogStore.get_isSome_iff s.log prevIdx).mp hsome).2

end StepLog

/--
**What a successful acknowledgement means.**

The only handler that emits `appendEntriesResp _ true _` is
`handleAppendEntries`, and only on the branch where the consistency check
passed. So a positive acknowledgement pins down the message that caused it, the
index it covers, and how the log was reshaped.
-/
theorem handleAppendEntries_ack {s : NodeState σ' κ'} [LogStore σ'] [LawfulLogStore σ'] [KVStore κ']
    {src term leaderId prevIdx prevTerm : Nat} {es : List Entry} {lc to t m : Nat}
    (h : Action.send to (Msg.appendEntriesResp t true m)
          ∈ (handleAppendEntries s src term leaderId prevIdx prevTerm es lc).2) :
    t = term ∧ m = prevIdx + es.length
      ∧ (handleAppendEntries s src term leaderId prevIdx prevTerm es lc).1.log
          = appendFrom s.log (prevIdx + 1) es
      ∧ prevIdx ≤ LogStore.lastIndex s.log
      ∧ (prevIdx ≠ 0 → LogStore.termAt s.log prevIdx = some prevTerm)
      ∧ s.currentTerm ≤ term
      ∧ (handleAppendEntries s src term leaderId prevIdx prevTerm es lc).1.role
          = Role.follower := by
  rw [handleAppendEntries] at h
  split at h
  · exact absurd (Msg.appendEntriesResp.inj (Action.send.inj (List.mem_singleton.mp h)).2).2.1
      (by simp)
  · rename_i hlt
    dsimp only at h
    have hmsd : (maybeStepDown s term (some leaderId)).1.log = s.log := by
      rw [maybeStepDown]; split <;> rfl
    have hmt : (maybeStepDown s term (some leaderId)).1.currentTerm = term := by
      rw [maybeStepDown_term]; omega
    split at h
    · rcases List.mem_append.mp h with h' | h'
      · exact absurd h' maybeStepDown_no_send
      · exact absurd
          (Msg.appendEntriesResp.inj (Action.send.inj (List.mem_singleton.mp h')).2).2.1 (by simp)
    · rename_i hcons
      have hc : ¬prevIdx = 0 → LogStore.termAt s.log prevIdx = some prevTerm := by
        simpa [hmsd] using hcons
      dsimp only at h
      rcases List.mem_append.mp h with h' | h'
      · exact absurd h' maybeStepDown_no_send
      · rcases List.mem_cons.mp h' with h'' | h''
        · have hm := (Action.send.inj h'').2
          obtain ⟨ht, _, hmi⟩ := Msg.appendEntriesResp.inj hm
          refine ⟨?_, hmi, ?_, ?_, hc, by omega, ?_⟩
          · rw [ht]; simp [hmt]
          · rw [handleAppendEntries, if_neg hlt]
            dsimp only
            rw [if_neg (by simpa using hcons)]
            dsimp only
            simp [hmsd]
          · rcases Nat.eq_zero_or_pos prevIdx with h0 | h0
            · omega
            · have hg := hc (by omega)
              have hsome : (LogStore.get s.log prevIdx).isSome := by
                cases hq : LogStore.get s.log prevIdx with
                | none => unfold LogStore.termAt at hg; rw [hq] at hg; simp at hg
                | some _ => rfl
              exact ((LogStore.get_isSome_iff s.log prevIdx).mp hsome).2
          · rw [handleAppendEntries, if_neg hlt]
            dsimp only
            rw [if_neg (by simpa using hcons)]
            dsimp only
            simp
        · exact absurd h'' applyCommitted_no_send

/-- **Complete description of how one step can change a node's log.** -/
theorem step_log {σ' : Type} [LogStore σ'] [LawfulLogStore σ'] {κ' : Type} [KVStore κ']
    (s : NodeState σ' κ') (ev : Event) :
    (Protocol.step s ev).1.log = s.log
      ∨ (∃ rid cmd, ev = Event.clientReq rid cmd
          ∧ (Protocol.step s ev).1.log
              = LogStore.append s.log { term := s.currentTerm, cmd := cmd, reqId := rid })
      ∨ (∃ src term l pi pt es lc,
          ev = Event.recv src (Msg.appendEntries term l pi pt es lc)
          ∧ (Protocol.step s ev).1.log = appendFrom s.log (pi + 1) es
          ∧ pi ≤ LogStore.lastIndex s.log
          ∧ (pi ≠ 0 → LogStore.termAt s.log pi = some pt)
          ∧ (Protocol.step s ev).1.role = Role.follower
          ∧ s.currentTerm ≤ term) := by
  cases ev with
  | recv src m =>
      cases m with
      | requestVote term candId li lt =>
          left
          rw [Protocol.step, handleRequestVote]
          split
          · rfl
          · have hmsd : (maybeStepDown s term none).1.log = s.log := by
              rw [maybeStepDown]; split <;> rfl
            dsimp only; split <;> simpa using hmsd
      | requestVoteResp term g =>
          left
          rw [Protocol.step, handleRequestVoteResp]
          split
          · rfl
          · split
            · rfl
            · dsimp only; split <;> (split <;> simp)
      | appendEntries term l pi pt es lc =>
          rcases handleAppendEntries_log (s := s) (src := src) (term := term) (leaderId := l)
            (prevIdx := pi) (prevTerm := pt) (es := es) (lc := lc) with h | ⟨h1, h2, h3, h4, h5⟩
          · exact Or.inl (by rw [Protocol.step]; exact h)
          · exact Or.inr (Or.inr ⟨src, term, l, pi, pt, es, lc, rfl,
              by rw [Protocol.step]; exact h1, h2, h3, by rw [Protocol.step]; exact h4, h5⟩)
      | appendEntriesResp term ok mi =>
          left
          rw [Protocol.step, handleAppendEntriesResp]
          split
          · rfl
          · split
            · rfl
            · split <;> simp
  | clientReq rid cmd =>
      by_cases hlead : s.role = Role.leader
      · exact Or.inr (Or.inl ⟨rid, cmd, rfl, by
          rw [Protocol.step]; exact handleClientReq_log hlead⟩)
      · left
        rw [Protocol.step, handleClientReq, if_pos (by simp [hlead])]
  | electionTimeout =>
      left
      rw [Protocol.step]
      split
      · rfl
      · rw [startElection]; dsimp only; split <;> rfl
  | heartbeatTimeout =>
      left
      rw [Protocol.step]; split <;> rfl

/-! ## A leader's log only grows -/

section LeaderLog

variable {κ : Type} [KVStore κ]

/--
**While a node remains leader, its log can only be extended by one entry.**

Truncation lives exclusively in `appendFrom`, which is reachable only through
`handleAppendEntries` — and that handler unconditionally demotes the node to
follower. So a node that is a leader both before and after an event either left
its log alone or appended a single client entry to the end.

This is the local half of "a leader's log is append-only during its term"; the
global half additionally needs that a node cannot leave and re-enter leadership
within one term, which follows from `everWinner_unique`.
-/
theorem step_log_of_leader (s : NodeState σ κ) (ev : Event)
    (hlold : s.role = Role.leader)
    (hl : (Protocol.step s ev).1.role = Role.leader) :
    (Protocol.step s ev).1.log = s.log
      ∨ ∃ e, (Protocol.step s ev).1.log = LogStore.append s.log e := by
  cases ev with
  | recv src m =>
      cases m with
      | requestVote term candId li lt =>
          left
          rw [Protocol.step, handleRequestVote] at hl ⊢
          by_cases hlt : term < s.currentTerm
          · rw [if_pos hlt]
          · by_cases hgt : term > s.currentTerm
            · exfalso
              rw [if_neg hlt] at hl
              dsimp only at hl
              have hr : (maybeStepDown s term none).1.role = Role.follower := by
                rw [maybeStepDown, if_pos hgt]; rfl
              revert hl; split <;> simp [hr]
            · have hmsd : (maybeStepDown s term none).1 = s := by
                rw [maybeStepDown, if_neg hgt]
              rw [if_neg hlt]
              dsimp only
              rw [hmsd]
              split <;> rfl
      | requestVoteResp term g =>
          left
          rw [Protocol.step, handleRequestVoteResp] at hl ⊢
          by_cases hgt : term > s.currentTerm
          · exfalso; rw [if_pos hgt, stepDown_role] at hl; exact Role.noConfusion hl
          · rw [if_neg hgt]
            by_cases hguard : s.role != Role.candidate || term != s.currentTerm || !g
            · rw [if_pos hguard]
            · exfalso
              simp only [Bool.not_eq_true, Bool.or_eq_false_iff, bne_eq_false_iff_eq,
                Bool.not_eq_false] at hguard
              rw [hlold] at hguard
              exact Role.noConfusion hguard.1.1
      | appendEntries term l pi pt es lc =>
          left
          rw [Protocol.step, handleAppendEntries] at hl ⊢
          by_cases hlt : term < s.currentTerm
          · rw [if_pos hlt]
          · exfalso
            rw [if_neg hlt] at hl
            dsimp only at hl
            revert hl
            split
            · simp
            · dsimp only; simp
      | appendEntriesResp term ok mi =>
          left
          rw [Protocol.step, handleAppendEntriesResp] at hl ⊢
          by_cases hgt : term > s.currentTerm
          · exfalso; rw [if_pos hgt, stepDown_role] at hl; exact Role.noConfusion hl
          · rw [if_neg hgt]
            by_cases hguard : s.role != Role.leader || term != s.currentTerm
            · rw [if_pos hguard]
            · rw [if_neg hguard]; split <;> simp
  | clientReq rid cmd =>
      rw [Protocol.step, handleClientReq] at hl ⊢
      by_cases hguard : s.role != Role.leader
      · left; rw [if_pos hguard]
      · right
        refine ⟨{ term := s.currentTerm, cmd := cmd, reqId := rid }, ?_⟩
        rw [if_neg hguard]
        dsimp only
        simp
  | electionTimeout =>
      left
      rw [Protocol.step] at hl ⊢
      by_cases hlead : s.role == Role.leader
      · rw [if_pos hlead]
      · exfalso
        rw [hlold] at hlead
        exact hlead (by simp)
  | heartbeatTimeout =>
      left
      rw [Protocol.step] at hl ⊢
      split <;> simp

end LeaderLog


/--
**A payload that already matches changes nothing.**

If every entry of the payload has the same term as the entry already sitting at
its index, `appendFrom` takes the keep-existing branch at every step and returns
the log unchanged — no truncation, so the tail beyond the payload survives.
-/
theorem appendFrom_id_of_match : ∀ (es : List Entry) (lg : σ) (startIdx : Nat),
    (∀ n e, es[n]? = some e →
      ∃ x, LogStore.get lg (startIdx + n) = some x ∧ x.term = e.term) →
    appendFrom lg startIdx es = lg := by
  intro es
  induction es with
  | nil => intro lg startIdx _; rfl
  | cons a es ih =>
      intro lg startIdx h
      obtain ⟨x, hx, hxt⟩ := h 0 a (by simp)
      rw [Nat.add_zero] at hx
      rw [appendFrom, hx]
      dsimp only
      rw [if_pos (by simp [hxt])]
      refine ih lg (startIdx + 1) ?_
      intro n e hn
      obtain ⟨y, hy, hyt⟩ := h (n + 1) e (by simpa using hn)
      exact ⟨y, by rw [show startIdx + 1 + n = startIdx + (n + 1) by omega]; exact hy, hyt⟩


/--
**A payload that matches below a bound leaves everything below it alone.**

The splice truncates only from its first conflicting index. If the payload
agrees with what is already stored at every index up to `B`, the first conflict
lies above `B`, so nothing at or below `B` moves.
-/
theorem appendFrom_match_below : ∀ (es : List Entry) (lg : σ) (startIdx B : Nat),
    startIdx ≤ LogStore.lastIndex lg + 1 →
    (∀ n e, es[n]? = some e → startIdx + n ≤ B →
      ∃ x, LogStore.get lg (startIdx + n) = some x ∧ x.term = e.term) →
    ∀ k, k ≤ B → LogStore.get (appendFrom lg startIdx es) k = LogStore.get lg k := by
  intro es
  induction es with
  | nil => intro lg startIdx B _ _ k _; rfl
  | cons a es ih =>
      intro lg startIdx B hb0 h k hk
      by_cases hb : startIdx ≤ B
      · obtain ⟨x, hx, hxt⟩ := h 0 a (by simp) (by omega)
        rw [Nat.add_zero] at hx
        have hle : startIdx ≤ LogStore.lastIndex lg :=
          ((LogStore.get_isSome_iff lg startIdx).mp (by rw [hx]; rfl)).2
        rw [appendFrom, hx]
        dsimp only
        rw [if_pos (by simp [hxt])]
        refine ih lg (startIdx + 1) B (by omega) ?_ k hk
        intro n e hn hle'
        obtain ⟨y, hy, hyt⟩ := h (n + 1) e (by simpa using hn) (by omega)
        exact ⟨y, by rw [show startIdx + 1 + n = startIdx + (n + 1) by omega]; exact hy, hyt⟩
      · exact appendFrom_get_of_lt (a :: es) lg startIdx k hb0 (by omega)


variable {κ' : Type} [KVStore κ']

/--
**Complete description of an `appendEntries` step, log and commit index together.**

Either the payload is rejected and neither moves, or it is accepted: the log is
the splice, the commit index rises to the leader's claim capped by the log's
end, and the node adopts the sender's term.
-/
theorem handleAppendEntries_shape {s : NodeState σ κ'}
    {src term leaderId prevIdx prevTerm : Nat} {es : List Entry} {lc : Nat} :
    ((handleAppendEntries s src term leaderId prevIdx prevTerm es lc).1.log = s.log
        ∧ (handleAppendEntries s src term leaderId prevIdx prevTerm es lc).1.commitIndex
            = s.commitIndex)
      ∨ ((handleAppendEntries s src term leaderId prevIdx prevTerm es lc).1.log
            = appendFrom s.log (prevIdx + 1) es
          ∧ (handleAppendEntries s src term leaderId prevIdx prevTerm es lc).1.commitIndex
              = max s.commitIndex
                  (min lc (LogStore.lastIndex (appendFrom s.log (prevIdx + 1) es)))
          ∧ prevIdx ≤ LogStore.lastIndex s.log
          ∧ (prevIdx ≠ 0 → LogStore.termAt s.log prevIdx = some prevTerm)
          ∧ s.currentTerm ≤ term) := by
  rw [handleAppendEntries]
  have hmsdL : (maybeStepDown s term (some leaderId)).1.log = s.log := by
    rw [maybeStepDown]; split <;> rfl
  have hmsdC : (maybeStepDown s term (some leaderId)).1.commitIndex = s.commitIndex := by
    rw [maybeStepDown]; split <;> rfl
  split
  · exact Or.inl ⟨rfl, rfl⟩
  · rename_i hlt
    dsimp only
    split
    · rename_i hcons
      exact Or.inl ⟨by simpa using hmsdL, by simpa using hmsdC⟩
    · rename_i hcons
      right
      refine ⟨by simp [hmsdL], by simp [hmsdL, hmsdC], ?_, ?_, by omega⟩
      · have hg : ¬prevIdx = 0 → LogStore.termAt s.log prevIdx = some prevTerm := by
          simpa [hmsdL] using hcons
        rcases Nat.eq_zero_or_pos prevIdx with h0 | h0
        · omega
        · have hsome : (LogStore.get s.log prevIdx).isSome := by
            have := hg (by omega)
            unfold LogStore.termAt at this
            cases hq : LogStore.get s.log prevIdx with
            | none => rw [hq] at this; simp at this
            | some z => rfl
          exact ((LogStore.get_isSome_iff s.log prevIdx).mp hsome).2
      · simpa [hmsdL] using hcons

end RaftKV.Proof
