import MathlibPlus.Basic

namespace MathlibPlus.Analysis

/-- A positive-leading real quadratic has the displayed unique global minimizer. -/
theorem claim21590_quadratic_minimum (A B C c : ℝ) (hA : 0 < A) :
    C - B ^ 2 / (4 * A) ≤ A * c ^ 2 + B * c + C ∧
      (A * c ^ 2 + B * c + C = C - B ^ 2 / (4 * A) ↔
        c = -B / (2 * A)) := by
  constructor
  · field_simp
    nlinarith [sq_nonneg (2 * A * c + B)]
  · constructor
    · intro h
      field_simp at h ⊢
      nlinarith [sq_nonneg (2 * A * c + B)]
    · intro hc
      subst c
      field_simp
      ring

end MathlibPlus.Analysis
