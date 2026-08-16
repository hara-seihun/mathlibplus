import Mathlib

namespace MathlibPlus.Open.LinearAlgebra

/--
At the one-atom anchor, the logarithmic first variation of the rank-four
completed Bezout determinant for the two-atom factorial-moment model.
-/
def primitiveSquarefreeLogDerivative : Prop :=
  let h : ℝ → ℕ → ℝ := fun ε j =>
    (1 + ε * ((1 : ℝ) / 4) ^ j) /
      ((Nat.factorial (2 * j) : ℕ) : ℝ)
  let C : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun ε i j =>
    Finset.sum (Finset.range (min i.val j.val + 1)) (fun a =>
      (((i.val + j.val + 1 - 2 * a : ℕ) : ℝ) *
        h ε a * h ε (i.val + j.val + 1 - a)))
  deriv (fun ε : ℝ => Matrix.det (C ε)) 0 /
      Matrix.det (C 0) = (-3901 : ℝ) / 16777216

end MathlibPlus.Open.LinearAlgebra
