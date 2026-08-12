import Mathlib

open scoped BigOperators

namespace MathlibPlus.Analysis

/-- Claim 18771: the pointwise `sinh` reparameterization preserves the
finite countermode moment equations. -/
theorem sinh_reparameterization_preserves_countermode_18771
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ ε : ℝ) (lam c : ι → ℝ) (R : ℕ)
    (hκ : κ ≠ 0) (hlam : ∀ j, lam j ≠ 0)
    (hc : ∀ r : ℕ, r < R → ∑ j, (lam j) ^ r * c j = 0) :
    let θ : ι → ℝ := fun j => Real.arsinh (ε * c j) / (κ * lam j)
    ((∀ j, Real.sinh (κ * lam j * θ j) = ε * c j) ∧
      (∀ r : ℕ, r < R →
        ∑ j, (lam j) ^ r * Real.sinh (κ * lam j * θ j) = 0)) := by
  dsimp
  have hpoint : ∀ j : ι,
      Real.sinh (κ * lam j * (Real.arsinh (ε * c j) / (κ * lam j))) = ε * c j := by
    intro j
    have hden : κ * lam j ≠ 0 := mul_ne_zero hκ (hlam j)
    have harg : κ * lam j * (Real.arsinh (ε * c j) / (κ * lam j)) =
        Real.arsinh (ε * c j) := by
      field_simp [hlam j]
    rw [harg, Real.sinh_arsinh]
  constructor
  · exact hpoint
  · intro r hr
    calc
      ∑ j, (lam j) ^ r * Real.sinh
          (κ * lam j * (Real.arsinh (ε * c j) / (κ * lam j))) =
          ∑ j, (lam j) ^ r * (ε * c j) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hpoint j]
      _ = ∑ j, ε * ((lam j) ^ r * c j) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = ε * ∑ j, (lam j) ^ r * c j := by
            rw [Finset.mul_sum]
      _ = 0 := by rw [hc r hr, mul_zero]

end MathlibPlus.Analysis
