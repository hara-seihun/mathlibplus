import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R0258

/-- The Schur monomial polynomial used in the modular logarithmic derivative claim. -/
def schurMonomialPolynomial (a : ℝ) (m : ℕ) : Polynomial ℂ :=
  Polynomial.C (a : ℂ) * Polynomial.X ^ m

/-- Evaluation of the Schur monomial at a complex argument. -/
def schurMonomial (a : ℝ) (m : ℕ) (z : ℂ) : ℂ :=
  (schurMonomialPolynomial a m).eval z

/-- The associated logarithmic derivative before simplifying the monomial. -/
def modularLogDerivative (a : ℝ) (m : ℕ) (z : ℂ) : ℂ :=
  (-2 : ℂ) * z * (schurMonomialPolynomial a m).derivative.eval z /
    (1 - schurMonomial a m z ^ 2)

/-- The explicit expression claimed for a Schur monomial. -/
def explicitModularLogDerivative (a : ℝ) (m : ℕ) (z : ℂ) : ℂ :=
  (-2 : ℂ) * (m : ℂ) * (a : ℂ) * z ^ m /
    (1 - (a : ℂ) ^ 2 * z ^ (2 * m))

/-- Claim 19260: the modular logarithmic derivative of a Schur monomial. -/
def claim19260 : Prop :=
  ∀ (a : ℝ) (m : ℕ) (z : ℂ),
    0 < a → a < 1 →
    1 - (a : ℂ) ^ 2 * z ^ (2 * m) ≠ 0 →
    modularLogDerivative a m z = explicitModularLogDerivative a m z

end MathlibPlus.Open.ResearchFormalization.R0258
