import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim4834

/-!
The packet names the profile, jet alternant, and confluent Vandermonde but does
not specify their source carrier.  A subtype records exactly the stated domain
`V_m ≠ 0`, so the quotient is not silently totalized at a zero denominator.
-/

/-- The normalized confluent Plücker coordinate on the nonzero Vandermonde locus. -/
def normalizedConfluentPluckerCoordinate
    {ι K : Type*} [Field K] (Δ V : ι → K) :
    {m : ι // V m ≠ 0} → K :=
  fun m => Δ m.1 / V m.1

/-- Multiplying the normalized coordinate by its denominator recovers the
original jet alternant. -/
theorem normalizedConfluentPluckerCoordinate_spec
    {ι K : Type*} [Field K] (Δ V : ι → K)
    (m : {m : ι // V m ≠ 0}) :
    V m.1 * normalizedConfluentPluckerCoordinate Δ V m = Δ m.1 := by
  change V m.1 * (Δ m.1 / V m.1) = Δ m.1
  exact mul_div_cancel₀ _ m.2

end MathlibPlus.LinearAlgebra.Claim4834
