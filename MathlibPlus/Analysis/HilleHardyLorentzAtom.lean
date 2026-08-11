import Mathlib

namespace MathlibPlus.Analysis.HilleHardyLorentzAtom

/-!
# Normalized Hille–Hardy Lorentz atom

Claim 19164 is the elementary determinant identity for the displayed
hyperbolic matrix. The two equalities are kept separate so that both the
matrix evaluation and the hyperbolic normalization remain visible.
-/

/-- For `B(ξ) = [[cosh ξ, sinh ξ], [sinh ξ, cosh ξ]]`, the determinant is one. -/
theorem normalizedLorentzAtom_determinant (ξ : ℝ) :
    let C : ℝ := Real.cosh ξ
    let S : ℝ := Real.sinh ξ
    Matrix.det !![C, S; S, C] = C ^ 2 - S ^ 2 ∧
      C ^ 2 - S ^ 2 = 1 := by
  dsimp
  constructor
  · rw [Matrix.det_fin_two_of]
    ring
  · exact Real.cosh_sq_sub_sinh_sq ξ

end MathlibPlus.Analysis.HilleHardyLorentzAtom
