-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

namespace MathlibPlus.AlgebraicGeometry.Claim11708

/-!
The projective point at infinity is represented by `none`; affine points are
represented by `some (x,y)`.  This records the claimed projective point count
without introducing an elliptic-curve projective-coordinate API.
-/

def curvePoints : Finset (Option (ZMod 5 × ZMod 5)) :=
  Finset.univ.filter (fun p =>
    p = none ∨ ∃ x y, p = some (x, y) ∧ y ^ 2 = x ^ 3 + x + 1)

/-- The curve `y² = x³ + x + 1` over `𝔽₅` has eight affine points and the
point at infinity, hence nine projective points. -/
theorem card_curvePoints_claim11708 : curvePoints.card = 9 := by
  native_decide

end MathlibPlus.AlgebraicGeometry.Claim11708
