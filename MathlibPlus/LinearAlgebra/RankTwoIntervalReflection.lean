import Mathlib

/-!
# Rank-two interval reflection

The exact rank-two matrix and eigenvector calculation from admitted claim `17904`.
The displayed quadratic-form witnesses make the asserted indefiniteness explicit.
-/

open scoped Matrix

namespace MathlibPlus.LinearAlgebra.RankTwoIntervalReflection

/-- The rank-two interval reflection `R_2^(0,2)`. -/
def rankTwoIntervalReflection : Matrix (Fin 2) (Fin 2) ℝ := !![0, 2; 2, 0]

/-- The eigenvector `(1,1)`. -/
def plusEigenvector : Fin 2 → ℝ := ![1, 1]

/-- The eigenvector `(1,-1)`. -/
def minusEigenvector : Fin 2 → ℝ := ![1, -1]

/-- The displayed vectors are nonzero. -/
theorem plusEigenvector_ne_zero : plusEigenvector ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 2)
  norm_num [plusEigenvector] at h0

theorem minusEigenvector_ne_zero : minusEigenvector ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 2)
  norm_num [minusEigenvector] at h0

/-- The two displayed vectors are eigenvectors with eigenvalues `2` and `-2`. -/
theorem rankTwoIntervalReflection_eigenvectors :
    rankTwoIntervalReflection *ᵥ plusEigenvector = (2 : ℝ) • plusEigenvector ∧
      rankTwoIntervalReflection *ᵥ minusEigenvector = (-2 : ℝ) • minusEigenvector := by
  constructor <;> ext i <;> fin_cases i <;>
    simp [rankTwoIntervalReflection, plusEigenvector, minusEigenvector, Matrix.mulVec,
      dotProduct]

/-- The two eigenvectors give positive and negative quadratic-form values. -/
theorem rankTwoIntervalReflection_indefinite_witness :
    0 < star plusEigenvector ⬝ᵥ (rankTwoIntervalReflection *ᵥ plusEigenvector) ∧
      star minusEigenvector ⬝ᵥ (rankTwoIntervalReflection *ᵥ minusEigenvector) < 0 := by
  norm_num [rankTwoIntervalReflection, plusEigenvector, minusEigenvector, Matrix.mulVec,
    dotProduct]

/-- The negative quadratic-form witness rules out positive semidefiniteness. -/
theorem rankTwoIntervalReflection_not_posSemidef :
    ¬ Matrix.PosSemidef rankTwoIntervalReflection := by
  intro h
  have hnonneg := h.dotProduct_mulVec_nonneg minusEigenvector
  norm_num [rankTwoIntervalReflection, minusEigenvector, Matrix.mulVec, dotProduct] at hnonneg

/-- Full formalization of the rank-two indefinite reflection claim. -/
theorem rankTwoIntervalReflection_claim :
    plusEigenvector ≠ 0 ∧
      minusEigenvector ≠ 0 ∧
      rankTwoIntervalReflection *ᵥ plusEigenvector = (2 : ℝ) • plusEigenvector ∧
      rankTwoIntervalReflection *ᵥ minusEigenvector = (-2 : ℝ) • minusEigenvector ∧
      0 < star plusEigenvector ⬝ᵥ (rankTwoIntervalReflection *ᵥ plusEigenvector) ∧
      star minusEigenvector ⬝ᵥ (rankTwoIntervalReflection *ᵥ minusEigenvector) < 0 ∧
      ¬ Matrix.PosSemidef rankTwoIntervalReflection := by
  exact ⟨plusEigenvector_ne_zero,
    minusEigenvector_ne_zero,
    rankTwoIntervalReflection_eigenvectors.1,
    rankTwoIntervalReflection_eigenvectors.2,
    rankTwoIntervalReflection_indefinite_witness.1,
    rankTwoIntervalReflection_indefinite_witness.2,
    rankTwoIntervalReflection_not_posSemidef⟩

end MathlibPlus.LinearAlgebra.RankTwoIntervalReflection
