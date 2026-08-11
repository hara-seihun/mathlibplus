import Mathlib

namespace MathlibPlus.Algebra.Claim13215

/-!
Claim 13215.  The reciprocal trace lift is stated over an arbitrary field and
at a nonzero value of the reciprocal variable, which is the domain on which
`x⁻¹` has its usual reciprocal meaning.
-/

/-- `x ^ 3 ( (x + x⁻¹)^3 - (x + x⁻¹) + 1)` is the displayed reciprocal
    polynomial `x⁶ + 2x⁴ + x³ + 2x² + 1`. -/
theorem reciprocalTraceLift {K : Type*} [Field K] (x : K) (hx : x ≠ 0) :
    let Q : K → K := fun t => t ^ 3 - t + 1
    let P : K → K := fun y => y ^ 6 + 2 * y ^ 4 + y ^ 3 + 2 * y ^ 2 + 1
    P x = x ^ 3 * Q (x + x⁻¹) := by
  dsimp
  field_simp [hx]
  ring

end MathlibPlus.Algebra.Claim13215
