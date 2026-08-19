import Mathlib

open scoped BigOperators

namespace MathlibPlus.Analysis.ThetaShellDerivative.Claim13860

noncomputable section

/-- The exact polynomial family in the theta-shell derivative recurrence. -/
noncomputable def thetaShellPolynomial (p : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | d + 1 =>
      (Polynomial.C p - 2 * Polynomial.X) * thetaShellPolynomial p d +
        2 * Polynomial.X * (thetaShellPolynomial p d).derivative

def thetaShellDerivativeRecurrence_claim13860 : Prop :=
  (∀ p : ℝ, thetaShellPolynomial p 0 = 1) ∧
    (∀ (p : ℝ) (d : ℕ) (y : ℝ),
      Polynomial.eval y (thetaShellPolynomial p (d + 1)) =
        (p - 2 * y) * Polynomial.eval y (thetaShellPolynomial p d) +
          2 * y * Polynomial.eval y (thetaShellPolynomial p d).derivative) ∧
    (∀ (p u : ℝ) (n d : ℕ),
      let y_n : ℝ := Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u)
      iteratedDeriv d
          (fun v : ℝ => Real.exp (p * v - Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * v))) u =
        Polynomial.eval y_n (thetaShellPolynomial p d) *
          Real.exp (p * u - y_n))

end

end MathlibPlus.Analysis.ThetaShellDerivative.Claim13860
