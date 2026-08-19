import Mathlib

namespace MathlibPlus.Algebra.R0298

/-- Claim 19535: an exactly divisible nonnegative numerator and divisor can
have a quotient with a negative coefficient. -/
def positiveCoefficientPolynomialSemiringNotDivisionClosed_claim19535 : Prop :=
  ∃ d q p : Polynomial ℤ,
    d * q = p ∧
    (∀ n : ℕ, 0 ≤ d.coeff n) ∧
    (∀ n : ℕ, 0 ≤ p.coeff n) ∧
    ¬ (∀ n : ℕ, 0 ≤ q.coeff n)

end MathlibPlus.Algebra.R0298
