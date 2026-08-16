import Mathlib

open scoped BigOperators
open MeasureTheory
open Set

noncomputable section

namespace MathlibPlus.Open.FormalizationBatch.FirstShell

/-- The generalized-Bell polynomial recurrence supplied with the admitted carrier. -/
def firstShellQ : ℕ → Polynomial ℝ
  | 0 => 2 * Polynomial.X - 3
  | n + 1 =>
      (Polynomial.C ((5 : ℝ) / 2) - 2 * Polynomial.X) * firstShellQ n +
        2 * Polynomial.X * (firstShellQ n).derivative

/-- The Wronskian polynomial built from the supplied Q-sequence. -/
def firstShellWronskian (r : ℕ) : Polynomial ℝ :=
  Matrix.det (fun i j : Fin r => firstShellQ (2 * i.1 + j.1))

/-- The polynomial P_r in the supplied exact Wronskian factorization. -/
def firstShellP (r : ℕ) : Polynomial ℝ :=
  firstShellWronskian r /ₘ (Polynomial.X ^ (r * (r - 1) / 2))

/-- The shifted polynomial whose coefficients form the first-shell chamber. -/
def shiftedFirstShellP (r : ℕ) : Polynomial ℝ :=
  (firstShellP r).comp
    (Polynomial.X + Polynomial.C (((2 * r - 1 : ℕ) : ℝ)))

/-- Shifted first-shell coefficients are positive through rank 23, with the
exact supplied Wronskian factorization and degree anchoring the named P_r. -/
def shiftedFirstShellCoefficientsPositiveThrough23 : Prop :=
  (∀ r : ℕ, 1 ≤ r → r ≤ 23 →
    firstShellWronskian r =
        Polynomial.X ^ (r * (r - 1) / 2) * firstShellP r ∧
      (firstShellP r).natDegree = r * (r + 1) / 2 ∧
      (∀ n : ℕ, n ≤ (shiftedFirstShellP r).natDegree →
        0 < (shiftedFirstShellP r).coeff n)) ∧
  (¬ ∃ r : ℕ, 1 ≤ r ∧ r ≤ 23 ∧
    ∃ n : ℕ, n ≤ (shiftedFirstShellP r).natDegree ∧
      (shiftedFirstShellP r).coeff n ≤ 0)


