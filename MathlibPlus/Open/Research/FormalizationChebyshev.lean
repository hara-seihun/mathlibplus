import Mathlib

namespace MathlibPlus.Open.Research

open scoped BigOperators

noncomputable section

/-- Admitted finite Chebyshev barycentric lower bound. -/
def claim3559 : Prop :=
  ∀ (d : ℕ) (ell : ℝ) (t : Fin (d + 1) → ℝ),
    0 < d →
    0 < ell →
    (∃ c : ℝ, ∀ j : Fin (d + 1), c ≤ t j ∧ t j ≤ c + ell) →
    (∀ i j : Fin (d + 1), i.1 < j.1 → t i < t j) →
    ∑ j : Fin (d + 1),
        |∏ k ∈ (Finset.univ.erase j), (t j - t k)⁻¹| ≥
      (2 : ℝ) ^ (2 * d - 1) / ell ^ d

end

end MathlibPlus.Open.Research
