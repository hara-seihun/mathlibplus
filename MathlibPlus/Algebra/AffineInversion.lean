-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib.Data.ZMod.Basic

namespace MathlibPlus.Algebra.AffineInversion

/-!
Formalization of admitted claim 37598.

The product `ZMod 3 × ZMod 3` is the standard coordinate model of `𝔽₃²`.
The affine inversion with translation `a` is written directly as `z ↦ -z + a`.
-/

/-- An affine inversion of `𝔽₃²` cannot fix two distinct points. -/
theorem affine_inversion_two_fixed_points
    (a x y : ZMod 3 × ZMod 3)
    (hx : -x + a = x)
    (hy : -y + a = y) :
    x = y := by
  native_decide +revert

end MathlibPlus.Algebra.AffineInversion
