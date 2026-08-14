import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

/-- The exact rank-three completed Bezout moment polynomial claim. -/
def rankThreeMomentPolynomial (m : ℕ → ℝ) : Prop :=
  let h : ℕ → ℝ := fun j => m j / (Nat.factorial (2 * j) : ℝ)
  let C : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
    ∑ a ∈ Finset.range (min i.val j.val + 1),
      (((i.val + j.val + 1 - 2 * a : ℕ) : ℝ) * h a *
        h (i.val + j.val + 1 - a))
  let D₃ : ℝ := 36578304000 * Matrix.det C
  D₃ =
    105 * (m 0)^3 * (m 1) * (m 3) * (m 5)
      - 180 * (m 0)^3 * (m 1) * (m 4)^2
      - 350 * (m 0)^3 * (m 2)^2 * (m 5)
      + 2520 * (m 0)^3 * (m 2) * (m 3) * (m 4)
      - 2646 * (m 0)^3 * (m 3)^3
      + 525 * (m 0)^2 * (m 1)^2 * (m 2) * (m 5)
      - 2205 * (m 0)^2 * (m 1)^2 * (m 3) * (m 4)
      - 9450 * (m 0)^2 * (m 1) * (m 2)^2 * (m 4)
      + 26460 * (m 0)^2 * (m 1) * (m 2) * (m 3)^2
      - 14700 * (m 0)^2 * (m 2)^3 * (m 3)
      + 14175 * (m 0) * (m 1)^3 * (m 2) * (m 4)
      - 35280 * (m 0) * (m 1)^3 * (m 3)^2
      + 22050 * (m 0) * (m 1)^2 * (m 2)^2 * (m 3)

end MathlibPlus.Open.Analysis
