import Mathlib.Tactic

namespace MathlibPlus.AlgebraicGeometry

/-!
The arithmetic positivity filter from claim 14598.  The source packet fixes
this check to the Chern pair `(c₁², c₂) = (3, 9)`; no surface-existence claim
is added here.
-/

/-- Claim 14598: both entries of the displayed Chern pair are positive. -/
theorem positivity_filter_claim14598 :
    (0 : ℚ) < 3 ∧ (0 : ℚ) < 9 := by
  norm_num

end MathlibPlus.AlgebraicGeometry
