import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.RO0293Claim13300

/-- Claim 13300: the source's second correction, with its displayed trace and
correction polynomials, gives the exact auxiliary pair q₂ and r₂. -/
def secondAuxiliaryPair_claim13300 : Prop :=
  let ell : Polynomial ℚ :=
    Polynomial.X ^ 5 + Polynomial.X ^ 4 - 5 * Polynomial.X ^ 3 -
      5 * Polynomial.X ^ 2 + 4 * Polynomial.X + 3
  let c₂ : Polynomial ℚ := Polynomial.X ^ 4 + 2 * Polynomial.X ^ 3 + 1
  let q₂ : Polynomial ℚ := ell - 2 * c₂
  let r₂ : Polynomial ℚ := (Polynomial.X + 1) * q₂ + Polynomial.X * c₂
  q₂ =
      Polynomial.X ^ 5 - Polynomial.X ^ 4 - 9 * Polynomial.X ^ 3 -
        5 * Polynomial.X ^ 2 + 4 * Polynomial.X + 1 ∧
    r₂ =
      Polynomial.X ^ 6 + Polynomial.X ^ 5 - 8 * Polynomial.X ^ 4 -
        14 * Polynomial.X ^ 3 - Polynomial.X ^ 2 + 6 * Polynomial.X + 1

end MathlibPlus.Open.ResearchFormalization.RO0293Claim13300
