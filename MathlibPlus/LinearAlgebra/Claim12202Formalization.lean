import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim12202Formalization

/-- The prime-cut conditional-negative-type identity, with the source's
feature map and metric represented by a finite real inner-product space and
its squared Hilbert distance. -/
theorem primeCutMetric_conditionalNegativeType_claim12202
    (ι E : Type*) [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (Phi : ι → E) (c : ι → ℝ) :
    (∑ A, c A = 0) →
      let d : ι → ι → ℝ := fun A B => ‖Phi A - Phi B‖ ^ 2
      (∑ A, ∑ B, c A * c B * d A B =
          -2 * ‖∑ A, c A • Phi A‖ ^ 2) ∧
        -2 * ‖∑ A, c A • Phi A‖ ^ 2 ≤ 0 := by
  intro hc
  dsimp
  constructor
  · have hinner := inner_sum_smul_sum_smul_of_sum_eq_zero
      (s₁ := Finset.univ) (w₁ := c) Phi hc
      (s₂ := Finset.univ) (w₂ := c) Phi hc
    rw [← real_inner_self_eq_norm_sq]
    rw [hinner]
    simp only [pow_two]
    ring
  · nlinarith [sq_nonneg (‖∑ A, c A • Phi A‖ : ℝ)]

end MathlibPlus.LinearAlgebra.Claim12202Formalization
