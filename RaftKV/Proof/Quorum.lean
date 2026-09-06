import RaftKV.Protocol.Types

/-!
# Quorum intersection

The one combinatorial fact the whole Raft safety argument rests on: **any two
majorities of the same cluster share a member**.

Everything else about elections follows from it. If two nodes both claimed
leadership in the same term, some single node voted for both — and a node casts
at most one vote per term.
-/

namespace RaftKV.Proof

open RaftKV

/-- A duplicate-free set of members that is large enough to be a quorum. -/
structure IsQuorum (c : Config) (v : List Nat) : Prop where
  /-- No node is counted twice. -/
  nodup : v.Nodup
  /-- Every voter is a cluster member. -/
  subset : ∀ x ∈ v, x ∈ c.members
  /-- At least `⌊n/2⌋ + 1` of them. -/
  large : v.length ≥ c.quorum

/--
**Quorum intersection.** Two quorums of the same configuration always share a
member.

The proof is a counting argument: were they disjoint, their concatenation would
be a duplicate-free sublist of the membership, forcing
`|v₁| + |v₂| ≤ n`; but two quorums have `|v₁| + |v₂| ≥ 2⌊n/2⌋ + 2 > n`.
-/
theorem quorum_intersect {c : Config} {v₁ v₂ : List Nat}
    (hm : c.members.Nodup) (h₁ : IsQuorum c v₁) (h₂ : IsQuorum c v₂) :
    ∃ x, x ∈ v₁ ∧ x ∈ v₂ := by
  apply Classical.byContradiction
  intro hcon
  -- Disjointness makes the concatenation duplicate-free.
  have hdisj : ∀ a ∈ v₁, ∀ b ∈ v₂, a ≠ b := by
    intro a ha b hb hab
    exact hcon ⟨a, ha, hab ▸ hb⟩
  have hnd : (v₁ ++ v₂).Nodup := by
    rw [List.nodup_append]
    exact ⟨h₁.nodup, h₂.nodup, hdisj⟩
  have hsub : v₁ ++ v₂ ⊆ c.members := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact h₁.subset a h
    · exact h₂.subset a h
  have hle : (v₁ ++ v₂).length ≤ c.members.length :=
    List.Nodup.length_le_of_subset hnd hsub
  rw [List.length_append] at hle
  -- But two quorums are jointly too large.
  have h1 := h₁.large
  have h2 := h₂.large
  have hq : c.quorum = c.members.length / 2 + 1 := rfl
  have hhalf : 2 * (c.members.length / 2) + 1 ≥ c.members.length := by omega
  omega

/-- A cluster whose membership list is duplicate-free. -/
def Config.WellFormed (c : Config) : Prop := c.members.Nodup ∧ c.me ∈ c.members

end RaftKV.Proof
