import Mathlib

/-!
# Mertens-product branch calculus

This file formalizes the exact elementary derivative calculation in Record 6 of
source record `C-0042`.  It does not formalize the packet's finite prime-jump
certificate, tail estimate, or sharp numerical constant.
-/

namespace MathlibPlus.MertensProduct

/-- On an interval where the Mertens prime product is the constant `A`, the
normalized error branch has the derivative stated in packet `C-0042`. -/
theorem productErrorBranch_hasDerivAt (A x : ℝ) (hx : 0 < x) :
    HasDerivAt
      (fun y => Real.log y *
        (Real.exp (-Real.eulerMascheroniConstant) * A - Real.log y))
      ((Real.exp (-Real.eulerMascheroniConstant) * A - 2 * Real.log x) / x) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have h := (Real.hasDerivAt_log hx0).mul
    ((hasDerivAt_const x (Real.exp (-Real.eulerMascheroniConstant) * A)).sub
      (Real.hasDerivAt_log hx0))
  convert h using 1 <;> try rfl
  field_simp [hx0]
  simp only [Pi.sub_apply]
  ring

end MathlibPlus.MertensProduct
