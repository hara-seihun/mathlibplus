import Mathlib

/-!
# Connected determinant cumulants

Algebraic formulas for connected coefficients assembled from normalized determinant
derivatives.
-/

namespace MathlibPlus.Algebra

/-- The connected three-label coefficient obtained from normalized first-,
second-, and third-order determinant derivatives. -/
def connectedThreeDefectCumulant
    (kIJK kIJ kIK kJK kI kJ kK : ℝ) : ℝ :=
  kIJK - kIJ * kK - kIK * kJ - kJK * kI + 2 * kI * kJ * kK

/-- Exact connected three-defect cumulant formula. -/
theorem connectedThreeDefectCumulant_eq
    (kIJK kIJ kIK kJK kI kJ kK : ℝ) :
    connectedThreeDefectCumulant kIJK kIJ kIK kJK kI kJ kK =
      kIJK - kIJ * kK - kIK * kJ - kJK * kI + 2 * kI * kJ * kK := by
  rfl

end MathlibPlus.Algebra
