import Mathlib

namespace MathlibPlus.Algebra.Claim4557

/-- The hostile reciprocal polynomial at `q = 9`. -/
noncomputable def hostileReciprocalPolynomial : Polynomial ℤ :=
  1 + 7 * Polynomial.X + 9 * Polynomial.X ^ 2

/-- Evaluation exposes exactly the displayed quadratic. -/
theorem hostileReciprocalPolynomial_eval (u : ℤ) :
    Polynomial.eval u hostileReciprocalPolynomial = 1 + 7 * u + 9 * u ^ 2 := by
  simp [hostileReciprocalPolynomial]

end MathlibPlus.Algebra.Claim4557
