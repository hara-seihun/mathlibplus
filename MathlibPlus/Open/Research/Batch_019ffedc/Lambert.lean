import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Arithmetic

def adjacentLambertDefect (a W d D : ℕ → ℝ) : Prop :=
  (∀ j, 0 < a j) ∧
  (∀ j, d j = Real.log (a j / a (j + 1))) ∧
  (∀ j, D j = d j - (W (j + 1) - W j))

def exactLambertGaugeCocycle : Prop :=
  ∀ (a W : ℕ → ℝ),
    (∀ j, 0 < a j) →
    let R : ℕ → ℝ := fun j => Real.log (8 * Real.pi * a j) + W j
    let D : ℕ → ℝ := fun j => Real.log (a j / a (j + 1)) - (W (j + 1) - W j)
    ∀ j J : ℕ, j < J →
      R j - R (j + 1) = D j ∧
      R j = R J +
        Finset.sum (Finset.range (J - j)) (fun r => D (j + r))

end MathlibPlus.Open.Arithmetic
