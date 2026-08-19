import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.RO0285Claim13206

open scoped LaurentPolynomial

/-- Claim 13206: multiplying the reciprocal trace substitution by the
nonnegative power dictated by the degree produces a nonzero integral ordinary
polynomial. -/
def reciprocalTraceSubstitution_integral_nonzero_claim13206 : Prop :=
  ∀ (A : Polynomial ℤ), A ≠ 0 →
    ∃ (P : Polynomial ℤ),
      P ≠ 0 ∧
        Polynomial.toLaurent P =
          LaurentPolynomial.T (A.natDegree : ℤ) *
            Polynomial.eval₂ LaurentPolynomial.C
              (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) A

end MathlibPlus.Open.ResearchFormalization.RO0285Claim13206
