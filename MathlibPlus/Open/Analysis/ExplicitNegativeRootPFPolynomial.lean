import Mathlib

namespace MathlibPlus.Open.Analysis

/-!
# Explicit Pólya-frequency polynomial

Statement-fidelity registry node for admitted claim 12038.  `PF∞` is made
explicit as nonnegativity of every finite Toeplitz minor of the coefficient
sequence.
-/

/-- The displayed product has the four displayed negative real zeros and its
coefficient sequence is Pólya-frequency of infinite order. -/
def explicitNegativeRootPFPolynomial : Prop :=
  let F : Polynomial ℝ :=
    ((1 : Polynomial ℝ) + Polynomial.C (1 / 3 : ℝ) * Polynomial.X) *
      ((1 : Polynomial ℝ) + 2 * Polynomial.X) *
      ((1 : Polynomial ℝ) + 5 * Polynomial.X) *
      ((1 : Polynomial ℝ) + 7 * Polynomial.X)
  let a : ℕ → ℝ := fun n => F.coeff n
  (∀ z : ℝ, F.eval z = 0 ↔
      z = -3 ∨ z = -(1 / 2 : ℝ) ∨ z = -(1 / 5 : ℝ) ∨ z = -(1 / 7 : ℝ)) ∧
    (0 : ℝ) > -3 ∧
    (0 : ℝ) > -(1 / 2 : ℝ) ∧
    (0 : ℝ) > -(1 / 5 : ℝ) ∧
    (0 : ℝ) > -(1 / 7 : ℝ) ∧
    ∀ r : ℕ, 1 ≤ r →
      ∀ rows cols : Fin r → ℕ, StrictMono rows → StrictMono cols →
        0 ≤ Matrix.det (fun i j : Fin r =>
          if rows i ≤ cols j then a (cols j - rows i) else 0)

end MathlibPlus.Open.Analysis
