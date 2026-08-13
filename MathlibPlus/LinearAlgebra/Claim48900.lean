import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim48900

/-- A componentwise bound on the diagonal weights propagates through the
quadratic-form estimate.  The source's matrix and depth-k objects are kept as
an explicit finite real interface rather than being silently reconstructed. -/
theorem quadraticBound_of_componentBounds
    {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (G lam : ι → ℝ) (C k : ℝ)
    (hlam : ∀ t, 0 < lam t)
    (hquad : ∀ x : ι → ℝ,
      (∑ i, x i * (M.mulVec x) i) ≤
        ∑ t, x t ^ 2 * G t / lam t)
    (hG : ∀ t, G t ≤ C * k) :
    ∀ x : ι → ℝ,
      (∑ i, x i * (M.mulVec x) i) ≤
        C * k * (∑ t, x t ^ 2 / lam t) := by
  intro x
  calc
    (∑ i, x i * (M.mulVec x) i) ≤
        ∑ t, x t ^ 2 * G t / lam t := hquad x
    _ = ∑ t, (x t ^ 2 / lam t) * G t := by
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ ≤ ∑ t, (x t ^ 2 / lam t) * (C * k) := by
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_left (hG t)
        (div_nonneg (sq_nonneg _) (le_of_lt (hlam t)))
    _ = C * k * (∑ t, x t ^ 2 / lam t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      ring

end MathlibPlus.LinearAlgebra.Claim48900
