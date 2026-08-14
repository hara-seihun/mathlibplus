import Mathlib

namespace MathlibPlus.Open.Algebra.ComponentPolynomialBatch

/-- Claim 34596: the singleton component variable is nonzero and cancellative
in an explicit component polynomial domain. -/
def claim34596 : Prop :=
  (MvPolynomial.X (1 : ℕ) : MvPolynomial ℕ ℤ) ≠ 0 ∧
    ∀ U_A U_B : MvPolynomial ℕ ℤ,
      MvPolynomial.X (1 : ℕ) * (U_A - U_B) = 0 → U_A = U_B

end MathlibPlus.Open.Algebra.ComponentPolynomialBatch
