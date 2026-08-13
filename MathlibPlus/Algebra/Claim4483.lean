import MathlibPlus.Algebra.Claim4485

open scoped BigOperators

namespace MathlibPlus.Algebra.Claim4483

open MathlibPlus.Algebra.Claim4485

/-- The zeroth two-variable complete homogeneous polynomial is one. -/
theorem completeHomogeneous_zero_claim4483 {R : Type*} [CommRing R] (a b : R) :
    completeHomogeneous 0 a b = 1 := by
  simp [completeHomogeneous]

/-- The first two-variable complete homogeneous polynomial is the sum of its variables. -/
theorem completeHomogeneous_one_claim4483 {R : Type*} [CommRing R] (a b : R) :
    completeHomogeneous 1 a b = a + b := by
  simp [completeHomogeneous, Finset.sum_range_succ]
  ring

end MathlibPlus.Algebra.Claim4483
