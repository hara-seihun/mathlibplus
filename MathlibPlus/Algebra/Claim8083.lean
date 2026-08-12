import Mathlib

namespace MathlibPlus.Algebra.Claim8083

/-- The algebraic Laurent-symbol quotient identity, after clearing the pole. -/
theorem bilateralLaurentSymbol_identity
    {K : Type*} [Field K]
    (C A z α : K) (hz : z ≠ α)
    (hA : A = C * (z - α) + 2 * α) :
    C + 2 * α / (z - α) = A / (z - α) := by
  rw [hA]
  field_simp [hz]

end MathlibPlus.Algebra.Claim8083
