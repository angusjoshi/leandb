import RaftKV.Proof.Candidate

/-!
# Log Matching for arbitrary well-formed logs

`logMatching` is stated about the logs replicas currently hold. Leader
Completeness needs the same reasoning about *snapshots* — the log a leader was
elected with, the log it committed against, the log a follower acknowledged.

The proof never used the fact that a log belonged to a live replica. It used
exactly two properties, isolated here as `WellFormedLog`: every entry was minted
at its index, and every entry beyond the first carries its predecessor link.
Node logs have them, and so does any snapshot of one, because `created` and
`chain` only ever grow.
-/

namespace RaftKV.Proof

open RaftKV Protocol

variable {σ κ : Type} [LogStore σ] [LawfulLogStore σ] [KVStore κ]

/-- A log whose entries are all accounted for in the ghost records. -/
structure WellFormedLog (w : World σ κ) (lg : σ) : Prop where
  /-- The log has discarded nothing: every recorded log is a logical one. -/
  nocompact : LogStore.firstIndex lg = 1
  /-- Every entry was minted at this index. -/
  created : ∀ k e, LogStore.get lg k = some e → ∃ c, (c, k, e) ∈ w.created
  /-- Every entry beyond the first carries its predecessor link. -/
  chained : ∀ k e, LogStore.get lg k = some e → 2 ≤ k →
    ∃ p, (k, e, p) ∈ w.chain ∧ LogStore.termAt lg (k - 1) = some p

/-- Replicas' own logs are well formed. -/
theorem wf_node {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) (i : Nat) :
    WellFormedLog w (w.full i) where
  nocompact := full_firstIndex hrch i
  created := fun k e h => (bInv_reachable hrch).logs i k e h
  chained := fun k e h hk => (chInv_reachable hnd hrch).logs i k e h hk

/-- Entries in well-formed logs are determined by index and term. -/
theorem wf_entry_unique {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) {lg₁ lg₂ : σ}
    (h₁ : WellFormedLog w lg₁) (h₂ : WellFormedLog w lg₂) {k : Nat} {e₁ e₂ : Entry}
    (g₁ : LogStore.get lg₁ k = some e₁) (g₂ : LogStore.get lg₂ k = some e₂)
    (hterm : e₁.term = e₂.term) : e₁ = e₂ := by
  obtain ⟨c₁, hc₁⟩ := h₁.created k e₁ g₁
  obtain ⟨c₂, hc₂⟩ := h₂.created k e₂ g₂
  exact entry_unique hnd hrch hc₁ hc₂ hterm

/-- Two well-formed logs sharing an entry share the entry beneath it. -/
theorem wf_agree_pred {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) {lg₁ lg₂ : σ}
    (h₁ : WellFormedLog w lg₁) (h₂ : WellFormedLog w lg₂) {idx : Nat} {e : Entry}
    (g₁ : LogStore.get lg₁ idx = some e) (g₂ : LogStore.get lg₂ idx = some e)
    (hidx : 2 ≤ idx) :
    LogStore.get lg₁ (idx - 1) = LogStore.get lg₂ (idx - 1) := by
  obtain ⟨p₁, hm₁, ht₁⟩ := h₁.chained idx e g₁ hidx
  obtain ⟨p₂, hm₂, ht₂⟩ := h₂.chained idx e g₂ hidx
  obtain ⟨v₁, hv₁⟩ : ∃ v, LogStore.get lg₁ (idx - 1) = some v := by
    unfold LogStore.termAt at ht₁
    cases hq : LogStore.get lg₁ (idx - 1) with
    | none => rw [hq] at ht₁; simp at ht₁
    | some v => exact ⟨v, rfl⟩
  obtain ⟨v₂, hv₂⟩ : ∃ v, LogStore.get lg₂ (idx - 1) = some v := by
    unfold LogStore.termAt at ht₂
    cases hq : LogStore.get lg₂ (idx - 1) with
    | none => rw [hq] at ht₂; simp at ht₂
    | some v => exact ⟨v, rfl⟩
  have hchain : p₁ = p₂ := (chInv_reachable hnd hrch).det idx e p₁ p₂ hm₁ hm₂
  have hterm : v₁.term = v₂.term := by
    unfold LogStore.termAt at ht₁ ht₂
    rw [hv₁] at ht₁; rw [hv₂] at ht₂
    have e₁ : v₁.term = p₁ := by simpa using ht₁
    have e₂ : v₂.term = p₂ := by simpa using ht₂
    rw [e₁, e₂, hchain]
  rw [hv₁, hv₂, wf_entry_unique hnd hrch h₁ h₂ hv₁ hv₂ hterm]

/--
**Log Matching for arbitrary well-formed logs.**

Two well-formed logs holding the same entry at an index are identical at every
index up to it.
-/
theorem wf_agree_below {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) {lg₁ lg₂ : σ}
    (h₁ : WellFormedLog w lg₁) (h₂ : WellFormedLog w lg₂) :
    ∀ (d idx : Nat) (e : Entry), idx ≤ d →
      LogStore.get lg₁ idx = some e → LogStore.get lg₂ idx = some e →
      ∀ k, k ≤ idx → LogStore.get lg₁ k = LogStore.get lg₂ k := by
  intro d
  induction d with
  | zero =>
      intro idx e hd g₁ _ k hk
      exact absurd g₁ (by rw [show idx = 0 by omega]; simp)
  | succ n ih =>
      intro idx e hd g₁ g₂ k hk
      by_cases hk0 : k = idx
      · subst hk0; rw [g₁, g₂]
      · by_cases hidx1 : idx ≤ 1
        · have hk00 : k = 0 := by omega
          subst hk00; simp
        have hidx2 : 2 ≤ idx := by omega
        have hpred := wf_agree_pred hnd hrch h₁ h₂ g₁ g₂ hidx2
        obtain ⟨v, hv⟩ : ∃ v, LogStore.get lg₁ (idx - 1) = some v := by
          cases hq : LogStore.get lg₁ (idx - 1) with
          | none =>
              exfalso
              have := get_isSome_below g₁ (m := idx - 1) (by rw [h₁.nocompact]; omega) (by omega)
              rw [hq] at this; exact Bool.noConfusion this
          | some v => exact ⟨v, rfl⟩
        exact ih (idx - 1) v (by omega) hv (by rw [← hpred]; exact hv) k (by omega)

/-- The convenient form: agreement at one index gives agreement below it. -/
theorem wf_matching {members : List Nat} {w : World σ κ}
    (hnd : members.Nodup) (hrch : Reachable members w) {lg₁ lg₂ : σ}
    (h₁ : WellFormedLog w lg₁) (h₂ : WellFormedLog w lg₂) {idx : Nat} {e : Entry}
    (g₁ : LogStore.get lg₁ idx = some e) (g₂ : LogStore.get lg₂ idx = some e) :
    ∀ k, k ≤ idx → LogStore.get lg₁ k = LogStore.get lg₂ k :=
  wf_agree_below hnd hrch h₁ h₂ idx idx e (Nat.le_refl _) g₁ g₂

end RaftKV.Proof
