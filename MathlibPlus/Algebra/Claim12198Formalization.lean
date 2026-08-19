import Mathlib

namespace MathlibPlus.Algebra.Claim12198Formalization

/-- Every homomorphism from an idempotent monoid to a group is trivial. -/
theorem everyHomFromIdempotentMonoidToGroup_trivial_claim12198
    {M G : Type*} [Monoid M] [Group G]
    (f : M →* G) (hIdem : ∀ x : M, x * x = x) :
    ∀ x : M, f x = 1 := by
  intro x
  have h : f x * f x = f x := by
    simpa [map_mul] using congrArg f (hIdem x)
  have h' : f x * f x = f x * 1 := by
    simpa using h
  exact mul_left_cancel h'

end MathlibPlus.Algebra.Claim12198Formalization
