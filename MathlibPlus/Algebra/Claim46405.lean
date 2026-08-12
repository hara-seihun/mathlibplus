import Mathlib

namespace MathlibPlus.Algebra.Claim46405

/-!
Formalization of the unambiguous displayed arithmetic in admitted claim 46405.
The packet explicitly flags the surrounding first-descent index convention for
fidelity review, so only the literal cross-product comparison is asserted.
-/

/-- The displayed tail comparison has left side 84, right side 78, and fails. -/
theorem tailComparisonFailure_46405 :
    (6 : ℤ) * 14 = 84 ∧
      (13 : ℤ) * 6 = 78 ∧
      (6 : ℤ) * 14 > 13 * 6 := by
  norm_num

end MathlibPlus.Algebra.Claim46405
