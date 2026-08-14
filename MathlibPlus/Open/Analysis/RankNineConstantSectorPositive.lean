import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable section

open scoped BigOperators

/-- The polynomial sequence in the admitted rank-nine claim. -/
def p : ℕ → Polynomial ℝ
  | 0 => 1
  | n + 1 =>
      Polynomial.X * Polynomial.derivative (p n) +
        (Polynomial.C (5 / 4 : ℝ) - Polynomial.X) * p n

/-- `g_j = p'_{2j}` for the eight indices `j = 1, ..., 8`. -/
def g (j : Fin 8) : Polynomial ℝ :=
  Polynomial.derivative (p (2 * (j.val + 1)))

/-- The determinant quotient in the admitted definition of `F₈`. -/
def f8 (x : Fin 8 → Polynomial ℝ) : Polynomial ℝ :=
  (Finset.prod (Finset.range 8) (fun k => (Nat.factorial k : Polynomial ℝ)) *
      Matrix.det (fun i j =>
        Polynomial.eval₂ (algebraMap ℝ (Polynomial ℝ)) (x i) (g j))) /
    Finset.prod Finset.univ (fun i =>
      Finset.prod (Finset.univ.filter (fun j : Fin 8 => i < j))
        (fun j => x j - x i))

/-- The eight substituted arguments `(2 + u) i²`, with `i = 1, ..., 8`. -/
def substitutedArgument (i : Fin 8) : Polynomial ℝ :=
  (Polynomial.C (2 : ℝ) + Polynomial.X) * Polynomial.C ((i.val + 1 : ℝ) ^ 2)

/-- Formal statement of the admitted positivity claim. -/
def rankNineConstantSectorPositive : Prop :=
  Polynomial.natDegree (f8 substitutedArgument) = 36 ∧
    ∀ m : ℕ, 0 ≤ m ∧ m ≤ 36 →
      0 < (f8 substitutedArgument).coeff m

end
end MathlibPlus.Open.Analysis
