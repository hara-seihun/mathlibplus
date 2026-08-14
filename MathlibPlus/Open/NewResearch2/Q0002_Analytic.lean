import Mathlib

open scoped BigOperators
open Polynomial

namespace MathlibPlus.Open.NewResearch2.Q0002.Analytic

noncomputable section

private def centralCharlier : ℕ → Polynomial ℚ
  | 0 => 1
  | n + 1 =>
      Polynomial.X * derivative (centralCharlier n) +
        (Polynomial.C (5 / 4) - Polynomial.X) * centralCharlier n

private def g (j : ℕ) : Polynomial ℚ := derivative (centralCharlier (2 * j))
private def T (f : Polynomial ℚ) : Polynomial ℚ :=
  g 1 * derivative f - derivative (g 1) * f

/-- The displayed projective-curvature counterexample. -/
def claim15719 : Prop :=
  T (g 2) =
      Polynomial.C ((1 : ℚ) / 4) *
        (64 * Polynomial.X ^ 3 - 432 * Polynomial.X ^ 2 +
          924 * Polynomial.X - 693) ∧
    (T (g 2)).eval 2 = (-61 : ℚ) / 4

/-- The displayed tangent--transversal determinant at `(2,8)`. -/
def claim15720 : Prop :=
  ((T (g 2)).eval 2 * (T (g 3)).eval 8 -
      (T (g 3)).eval 2 * (T (g 2)).eval 8) / (8 - 2) =
    (-4386309 : ℚ) / 32

end
end MathlibPlus.Open.NewResearch2.Q0002.Analytic
