import Mathlib

namespace MathlibPlus.Algebra.R0299

/-- A polynomial has mixed coefficients when it has both a positive and a
negative coefficient. -/
def mixedIntegerPolynomial19541 (b : Polynomial ℤ) : Prop :=
  (∃ n : ℕ, 0 < b.coeff n) ∧
    (∃ n : ℕ, b.coeff n < 0)

/-- Claim 19541: positive and sign monomial gauges only shift or globally
negate a mixed coefficient sequence; neither removes mixed signs. -/
def monomialGaugesCannotRepairMixedCoefficients_claim19541 : Prop :=
  ∀ b : Polynomial ℤ,
    mixedIntegerPolynomial19541 b →
      (∀ k : ℕ,
        mixedIntegerPolynomial19541 (Polynomial.X ^ k * b)) ∧
      (∀ k : ℕ,
        mixedIntegerPolynomial19541 (-(Polynomial.X ^ k) * b))

end MathlibPlus.Algebra.R0299
