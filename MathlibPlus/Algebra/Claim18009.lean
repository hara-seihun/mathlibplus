import Mathlib

namespace MathlibPlus.Algebra.Claim18009

/-!
Formalization of the constant/vacuum part of admitted claim 18009.  The
relative Euler operator is represented pointwise by
`w * ∂_w - z * ∂_z`; the two partial derivatives of a constant vanish.
-/

/-- The relative Euler operator annihilates every constant, in particular the
constant `1` vacuum. -/
theorem relativeEuler_annihilates_constant_claim18009
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] (c w z : 𝕜) :
    w * deriv (fun _ : 𝕜 => c) w -
        z * deriv (fun _ : 𝕜 => c) z = 0 := by
  simp

end MathlibPlus.Algebra.Claim18009
