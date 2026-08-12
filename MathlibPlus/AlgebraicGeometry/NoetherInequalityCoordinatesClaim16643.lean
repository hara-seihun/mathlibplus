import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith

namespace MathlibPlus.AlgebraicGeometry

/-- The coordinate translation in claim 16643, over integral Chern-number
coordinates.  No geometric existence assertion is included. -/
theorem noetherInequalityCoordinates_claim16643
    (K2 c1sq c2 chi : ℤ)
    (hK : K2 = c1sq)
    (hc2 : c2 = 12 * chi - K2) :
    (5 * c1sq ≥ c2 - 36) ↔ K2 ≥ 2 * chi - 6 := by
  constructor <;> intro h
  · linarith
  · linarith

end MathlibPlus.AlgebraicGeometry
