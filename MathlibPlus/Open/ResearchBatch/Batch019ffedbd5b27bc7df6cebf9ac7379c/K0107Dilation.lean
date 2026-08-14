import Mathlib

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.ResearchBatch.K0107

/-- The node polynomial of a finite list of real nodes. -/
def nodePolynomial {n : ℕ} (x : Fin n → ℝ) : Polynomial ℝ :=
  Finset.prod Finset.univ (fun i => Polynomial.X - Polynomial.C (x i))

/-- The dual weight convention used in the dilation statement. -/
def dualWeight {n : ℕ} (x w : Fin n → ℝ) (i : Fin n) : ℝ :=
  w i /
    ((nodePolynomial x).derivative.eval (x i)) ^ 2

/-- Exact derivative and dual-weight covariance under node dilation. -/
def claim8620 : Prop :=
  ∀ (n : ℕ) (x w : Fin n → ℝ) (c : ℝ),
    0 < c →
    (∀ i,
      ((nodePolynomial (fun j => c * x j)).derivative.eval (c * x i)) =
        c ^ (n - 1) * (nodePolynomial x).derivative.eval (x i)) ∧
    (∀ i,
      dualWeight (fun j => c * x j) w i =
        (c⁻¹) ^ (2 * (n - 1)) * dualWeight x w i)

end MathlibPlus.Open.ResearchBatch.K0107
