import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.C0043Claim684

open scoped BigOperators

noncomputable section

/-- The degree-thirteen product witness with its two nonnegative reciprocal
parameters. -/
def witnessPolynomial : Polynomial ℝ :=
  (1 + Polynomial.C 162 * Polynomial.X) ^ 2 *
    (1 + Polynomial.X) ^ 11

/-- The shifted fourth-order derivative determinant used for D₄. -/
noncomputable def fourthProductDeterminant (G : Polynomial ℝ) : ℝ :=
  Matrix.det (fun i j : Fin 4 =>
    Polynomial.eval 0 ((Polynomial.derivative^[3 + (j : ℕ) - (i : ℕ)]) G))

/-- Claim 684: the explicit degree-thirteen product has nonnegative reciprocal
parameters and the displayed strictly negative fourth determinant. -/
def claim684 : Prop :=
  witnessPolynomial.natDegree = 13 ∧
    (0 : ℝ) ≤ 162 ∧
    (0 : ℝ) ≤ 1 ∧
    fourthProductDeterminant witnessPolynomial = -527889869252540784 ∧
    fourthProductDeterminant witnessPolynomial < 0

end
end MathlibPlus.Open.ResearchFormalization.C0043Claim684
