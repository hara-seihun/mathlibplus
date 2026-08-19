import Mathlib

namespace MathlibPlus.Open.Algebra.PointwiseCoefficientClaim1586

noncomputable section

/-- The polynomial witness in admitted claim 1586. -/
def counterexamplePolynomial : Polynomial ℝ :=
  Polynomial.X ^ 2 - Polynomial.X + 1

/-- Coefficientwise nonnegativity for an exact cleared polynomial. -/
def coefficientwiseNonnegative (p : Polynomial ℝ) : Prop :=
  ∀ n : ℕ, 0 ≤ p.coeff n

/-- Positivity on a finite collection of numerical test values. -/
def positiveOnFiniteSample (p : Polynomial ℝ) (S : Finset ℝ) : Prop :=
  ∀ b ∈ S, 0 < p.eval b

/-- Positivity at every real argument. -/
def pointwisePositive (p : Polynomial ℝ) : Prop :=
  ∀ b : ℝ, 0 < p.eval b

/-- Pointwise and finite-sample positivity do not replace coefficientwise
positivity for the exact polynomial data in the recurrence. -/
def pointwisePositivityDoesNotImplyCoefficientwisePositivity_claim1586 : Prop :=
  let p : Polynomial ℝ := counterexamplePolynomial
  pointwisePositive p ∧
    (∀ b : ℝ, 0 ≤ b → 0 < p.eval b) ∧
    p.coeff 1 = (-1 : ℝ) ∧
    ¬ coefficientwiseNonnegative p ∧
    ¬ (pointwisePositive p → coefficientwiseNonnegative p) ∧
    ∀ S : Finset ℝ,
      positiveOnFiniteSample p S ∧ ¬ coefficientwiseNonnegative p

end
end MathlibPlus.Open.Algebra.PointwiseCoefficientClaim1586
