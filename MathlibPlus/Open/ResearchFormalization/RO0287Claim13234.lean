import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.RO0287Claim13234

/-- Claim 13234: the displayed degree-seven trace polynomial has the exact
reciprocal lift `P(x) = x^7 Q(x + x⁻¹)`, on the natural nonzero reciprocal
variable domain. -/
def reciprocalTraceLift_claim13234 : Prop :=
  ∀ {K : Type*} [Field K] (x : K), x ≠ 0 →
    let Q : Polynomial K :=
      Polynomial.X ^ 7 - 8 * Polynomial.X ^ 5 +
        19 * Polynomial.X ^ 3 - 12 * Polynomial.X + 1
    let P : Polynomial K :=
      Polynomial.X ^ 14 - Polynomial.X ^ 12 +
        Polynomial.X ^ 7 - Polynomial.X ^ 2 + 1
    Polynomial.eval x P =
      x ^ 7 * Polynomial.eval (x + x⁻¹) Q

end MathlibPlus.Open.ResearchFormalization.RO0287Claim13234
