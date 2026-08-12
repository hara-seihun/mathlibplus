import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs

namespace MathlibPlus.Algebra

/-- The ring formulation of direct (Dedekind) finiteness. -/
theorem directlyFinite_iff_isDedekindFiniteMonoid (R : Type*) [Ring R] :
    IsDedekindFiniteMonoid R ↔ ∀ x y : R, x * y = 1 → y * x = 1 := by
  constructor
  · intro h x y hxy
    exact @IsDedekindFiniteMonoid.mul_eq_one_symm R _ h x y hxy
  · intro h
    exact { mul_eq_one_symm := fun hxy => h _ _ hxy }

end MathlibPlus.Algebra
