import Mathlib

namespace MathlibPlus.AlgebraicGeometry.RoutineClaimFormalizations

/-- The numerical Chern-number consequence of the displayed Noether calculation
in claim 50117.  The geometric surface and moduli-existence carriers remain
outside this arithmetic statement. -/
theorem noether_c2_eq_seven_claim50117
    (chi c1Sq c2 : ℤ)
    (hchi : chi = 1)
    (hc1 : c1Sq = 5)
    (hNoether : c1Sq + c2 = 12 * chi) :
    c2 = 7 := by
  omega

end MathlibPlus.AlgebraicGeometry.RoutineClaimFormalizations
