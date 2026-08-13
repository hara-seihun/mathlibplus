import Mathlib

open Set
open Polynomial

namespace MathlibPlus.Analysis

/-- The integral cubic and linear polynomial in claim 22813 have resultant -1.
The coefficient field is `ℚ`, while all displayed coefficients are integral. -/
theorem integral_cubic_unit_resultant_claim22813 :
    Polynomial.resultant
        (C (1 : ℚ) * X ^ 3 + C 0 * X ^ 2 + C (-7) * X + C (-7))
        (C (2 : ℚ) * X + C 3) = -1 := by
  let fQ : Polynomial ℚ := C 1 * X ^ 3 + C 0 * X ^ 2 + C (-7) * X + C (-7)
  let dQ : Polynomial ℚ := C 2 * X + C 3
  have hf : fQ.natDegree ≤ 3 := by
    dsimp [fQ]
    rw [natDegree_cubic (by norm_num : (1 : ℚ) ≠ 0)]
  have hfd : dQ = C (2 : ℚ) * (X - C ((-3 : ℚ) / 2)) := by
    dsimp [dQ]
    rw [mul_sub]
    rw [← C_mul]
    norm_num
  have hdegf : fQ.natDegree = 3 := by
    dsimp [fQ]
    exact natDegree_cubic (by norm_num : (1 : ℚ) ≠ 0)
  have hdegd : dQ.natDegree = 1 := by
    dsimp [dQ]
    exact natDegree_linear (by norm_num : (2 : ℚ) ≠ 0)
  rw [show Polynomial.resultant fQ dQ = Polynomial.resultant fQ dQ 3 1 by
    rw [hdegf, hdegd]]
  rw [hfd, Polynomial.resultant_C_mul_right,
    Polynomial.resultant_X_sub_C_right fQ 3 ((-3 : ℚ) / 2) hf]
  dsimp [fQ]
  norm_num [Polynomial.eval₂_at_apply]

/-- The two negative interior roots isolated in claim 22813. -/
theorem interior_trace_roots_claim22813 : ∃ u₁ u₂ : ℝ,
    u₁ ^ 3 - 7 * u₁ - 7 = 0 ∧
    u₂ ^ 3 - 7 * u₂ - 7 = 0 ∧
    (-2 : ℝ) < u₁ ∧ u₁ < -3 / 2 ∧
    -3 / 2 < u₂ ∧ u₂ < -4 / 3 := by
  let f : ℝ → ℝ := fun x => x ^ 3 - 7 * x - 7
  have hf : Continuous f := by fun_prop
  have h₁ : ∃ u₁ : ℝ, f u₁ = 0 ∧ (-2 : ℝ) < u₁ ∧ u₁ < -3 / 2 := by
    have hval : (0 : ℝ) ∈ Ioo (f (-2)) (f (-3 / 2)) := by
      dsimp [f]
      norm_num
    rcases intermediate_value_Ioo (show (-2 : ℝ) ≤ -3 / 2 by norm_num)
      hf.continuousOn hval with ⟨u, hu, hfu⟩
    exact ⟨u, hfu, hu.1, hu.2⟩
  have h₂ : ∃ u₂ : ℝ, f u₂ = 0 ∧ (-3 / 2 : ℝ) < u₂ ∧ u₂ < -4 / 3 := by
    have hval : (0 : ℝ) ∈ Ioo (f (-4 / 3)) (f (-3 / 2)) := by
      dsimp [f]
      norm_num
    rcases intermediate_value_Ioo' (show (-3 / 2 : ℝ) ≤ -4 / 3 by norm_num)
      hf.continuousOn hval with ⟨u, hu, hfu⟩
    exact ⟨u, hfu, hu.1, hu.2⟩
  rcases h₁ with ⟨u₁, hu₁, h₁a, h₁b⟩
  rcases h₂ with ⟨u₂, hu₂, h₂a, h₂b⟩
  exact ⟨u₁, u₂, by simpa [f] using hu₁, by simpa [f] using hu₂,
    h₁a, h₁b, h₂a, h₂b⟩

end MathlibPlus.Analysis
