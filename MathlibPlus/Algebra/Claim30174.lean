import Mathlib

namespace MathlibPlus.Algebra.Claim30174

/--
The affine plane shear is stated without choosing coefficients silently: the
hypothesis explicitly says that `f` is the affine map `x ↦ a*x+b`, and the
triple-coordinate shear is then the displayed map from the claim.
-/
theorem affine_plane_shear_formula
    {R : Type*} [Ring R] (f : R → R) (a b z x u : R)
    (hf : ∀ y, f y = a * y + b) :
    let Lf : R × R × R → R × R × R :=
      fun p => (p.1 + f p.2.1, p.2.1, p.2.2)
    Lf (z, x, u) = (z + (a * x + b), x, u) := by
  dsimp
  rw [hf x]

end MathlibPlus.Algebra.Claim30174
