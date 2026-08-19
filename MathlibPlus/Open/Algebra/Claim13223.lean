import Mathlib
import MathlibPlus.Open.Algebra.Claim13222ModularFactorDegrees

open scoped Polynomial
open Polynomial

namespace MathlibPlus.Open.Algebra.Claim13223

/-- The fixed exterior polynomial is irreducible over `ℚ`. -/
def claim13223 : Prop :=
  let F : ℤ[X] :=
    X ^ 12 + X ^ 11 - C (2 : ℤ) * X ^ 10 - C (2 : ℤ) * X ^ 9 +
      X ^ 8 - C (5 : ℤ) * X ^ 7 - C (11 : ℤ) * X ^ 6 -
      C (5 : ℤ) * X ^ 5 + X ^ 4 - C (2 : ℤ) * X ^ 3 -
      C (2 : ℤ) * X ^ 2 + X + C (1 : ℤ)
  Irreducible (F.map (Int.castRingHom ℚ))

end MathlibPlus.Open.Algebra.Claim13223
