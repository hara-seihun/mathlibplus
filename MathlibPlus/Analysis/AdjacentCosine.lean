import Mathlib

namespace MathlibPlus.Analysis.AdjacentCosine

private theorem cosine_square_sum (φ θ : ℝ) :
    Real.cos φ ^ 2 + Real.cos (φ + θ) ^ 2 =
      1 + Real.cos (2 * φ + θ) * Real.cos θ := by
  rw [Real.cos_sq, Real.cos_sq]
  have hcos : Real.cos (2 * (φ + θ)) = Real.cos (2 * φ + 2 * θ) := by
    congr 1 <;> ring
  rw [hcos]
  have hsum : Real.cos (2 * φ) + Real.cos (2 * φ + 2 * θ) =
      2 * Real.cos (2 * φ + θ) * Real.cos θ := by
    calc
      Real.cos (2 * φ) + Real.cos (2 * φ + 2 * θ) =
          Real.cos ((2 * φ + θ) - θ) + Real.cos ((2 * φ + θ) + θ) := by
            congr 1 <;> ring
      _ = 2 * Real.cos (2 * φ + θ) * Real.cos θ := by
        simp only [Real.cos_sub, Real.cos_add]
        ring
  nlinarith [hsum]

theorem exact_adjacent_cosine_lower_eigenvalue (φ θ : ℝ) :
    1 - |Real.cos θ| ≤ Real.cos φ ^ 2 + Real.cos (φ + θ) ^ 2 := by
  rw [cosine_square_sum]
  have hθlo : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
  have hθhi : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hφθlo : -1 ≤ Real.cos (2 * φ + θ) :=
    Real.neg_one_le_cos (2 * φ + θ)
  have hφθhi : Real.cos (2 * φ + θ) ≤ 1 :=
    Real.cos_le_one (2 * φ + θ)
  by_cases h : 0 ≤ Real.cos θ
  · rw [abs_of_nonneg h]
    nlinarith [mul_le_mul_of_nonneg_left hφθlo h]
  · have h' : Real.cos θ ≤ 0 := le_of_not_ge h
    rw [abs_of_nonpos h']
    nlinarith [mul_le_mul_of_nonpos_left hφθhi h']

end MathlibPlus.Analysis.AdjacentCosine
