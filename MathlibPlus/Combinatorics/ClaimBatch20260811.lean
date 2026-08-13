import Mathlib

open scoped BigOperators

namespace MathlibPlus.Combinatorics.ClaimBatch20260811

/-- Claim 31756: if positive component orders sum to `r` with
`J ≤ r < 2J`, two distinct components cannot both have order `J`. -/
theorem oneLargestMarkerForest_claim31756
    {ι : Type*} [Fintype ι]
    (J r : ℕ) (_hJ : 0 < J) (_hrJ : J ≤ r) (hr2J : r < 2 * J)
    (order : ι → ℕ) (_hpos : ∀ i, 0 < order i)
    (hsum : ∑ i, order i = r) :
    ∀ i j, order i = J → order j = J → i = j := by
  intro i j hi hj
  by_contra hij
  classical
  have hsum_i : order i ≤ ∑ k, order k := by
    exact Finset.single_le_sum (fun k _ => Nat.zero_le (order k)) (Finset.mem_univ i)
  have hsum_j : order j ≤ ∑ k, order k := by
    exact Finset.single_le_sum (fun k _ => Nat.zero_le (order k)) (Finset.mem_univ j)
  have htwo : 2 * J ≤ ∑ k, order k := by
    -- Separate the two distinct summands by deleting `i`.
    have hrest : order j ≤ (Finset.univ.erase i).sum order := by
      apply Finset.single_le_sum (fun k _ => Nat.zero_le (order k))
      simpa using (Ne.symm hij)
    have hdecomp : order i + (Finset.univ.erase i).sum order = ∑ k, order k := by
      calc
        order i + (Finset.univ.erase i).sum order =
            (Finset.univ.erase i).sum order + order i := Nat.add_comm _ _
        _ = ∑ k, order k := Finset.sum_erase_add _ _ (Finset.mem_univ i)
    rw [← hdecomp]
    omega
  rw [hsum] at htwo
  exact (Nat.not_lt_of_ge htwo) hr2J

/-- Claim 42092: incidence one makes the orbit blocks a partition of the
root set. -/
theorem incidenceOnePartitionsRoots_claim42092
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (block : β → Finset α)
    (hone : ∀ x : α, ∃! b : β, x ∈ block b) :
    (∀ b₁ b₂ : β, b₁ ≠ b₂ → Disjoint (block b₁) (block b₂)) ∧
      (Finset.biUnion Finset.univ block = Finset.univ) := by
  constructor
  · intro b₁ b₂ hne
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    rcases hone x with ⟨b, hb, huniq⟩
    have h₁ : b₁ = b := huniq b₁ hx₁
    have h₂ : b₂ = b := huniq b₂ hx₂
    exact hne (h₁.trans h₂.symm)
  · ext x
    constructor
    · intro _
      exact Finset.mem_univ _
    · intro _
      rcases hone x with ⟨b, hb, _⟩
      exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, hb⟩

end MathlibPlus.Combinatorics.ClaimBatch20260811
