import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchO0080

noncomputable def primitiveG6 (u : ℝ) : ℝ :=
  (1 / 12 : ℝ) *
    ∑ n ∈ Finset.Icc 1 (Nat.floor (Real.exp u)),
      (((n : ℝ) / Real.exp u) ^ 2) *
        (1 - ((n : ℝ) / Real.exp u) ^ 2) ^ 4

noncomputable def centeredPrimitive (u : ℝ) : ℝ :=
  primitiveG6 u - (32 / 10395 : ℝ) * Real.exp u

/-- The admitted centered m=6 primitive, including its two exact lattice
formulae, signs, and the three witnesses in every sufficiently large
logarithmic unit cell. -/
def claim12172 : Prop :=
  (∀ N : ℕ, 1 ≤ N →
    centeredPrimitive (Real.log (N : ℝ)) =
      (1760 * (N : ℝ) ^ 4 - 2541 * (N : ℝ) ^ 2 + 525) /
        (83160 * (N : ℝ) ^ 9)) ∧
  centeredPrimitive (Real.log (1 : ℝ)) < 0 ∧
  (∀ N : ℕ, 2 ≤ N →
    0 < centeredPrimitive (Real.log (N : ℝ))) ∧
  (∀ N : ℕ, 1 ≤ N →
    centeredPrimitive (Real.log ((N : ℝ) + (1 : ℝ) / 2)) =
      -(872960 * ((N : ℝ) + (1 : ℝ) / 2) ^ 4 -
          1290828 * ((N : ℝ) + (1 : ℝ) / 2) ^ 2 + 268275) /
        (42577920 * ((N : ℝ) + (1 : ℝ) / 2) ^ 9)) ∧
  (∀ N : ℕ, 1 ≤ N →
    centeredPrimitive (Real.log ((N : ℝ) + (1 : ℝ) / 2)) < 0) ∧
  (∀ N : ℕ, 2 ≤ N →
    0 < centeredPrimitive (Real.log (N : ℝ)) ∧
      centeredPrimitive (Real.log ((N : ℝ) + (1 : ℝ) / 2)) < 0 ∧
      0 < centeredPrimitive (Real.log ((N + 1 : ℕ) : ℝ)))

end MathlibPlus.Open.ResearchFormalization.BatchO0080
