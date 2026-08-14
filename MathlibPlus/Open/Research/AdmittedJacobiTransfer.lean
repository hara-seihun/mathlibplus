import Mathlib

namespace MathlibPlus.Open.Research

open Polynomial

def polynomialMovingEnergyAndComparisonBounds : Prop :=
  ∀ (N : ℕ) (ρ x : ℝ) (a : ℤ → ℝ) (p : ℤ → Polynomial ℝ),
    2 ≤ N →
    0 < ρ →
    ρ < 1 →
    (∀ j : ℤ, 1 ≤ j → j < (N : ℤ) → 0 < a j) →
    p (-1 : ℤ) = 0 →
    p 0 = 1 →
    (∀ j : ℤ, 0 ≤ j → j < (N : ℤ) →
      C (a (j + 1)) * p (j + 1) =
        X * p j - C (a j) * p (j - 1)) →
    let Q : ℤ → ℝ := fun j =>
      a j * (eval x (p j) ^ 2 + eval x (p (j - 1)) ^ 2) -
        x * eval x (p j) * eval x (p (j - 1))
    (∀ j : ℤ, 1 ≤ j → j < (N : ℤ) → |x| ≤ 2 * ρ * a j →
      (1 - ρ) * a j * (eval x (p j) ^ 2 + eval x (p (j - 1)) ^ 2) ≤ Q j ∧
      Q j ≤ (1 + ρ) * a j * (eval x (p j) ^ 2 + eval x (p (j - 1)) ^ 2)) ∧
    Q 1 = a 1

def zeroDiagonalJacobiRecurrenceAndTransfer : Prop :=
  ∀ (N : ℕ) (a : ℤ → ℝ) (p : ℤ → Polynomial ℝ),
    2 ≤ N →
    (∀ j : ℤ, 1 ≤ j → j < (N : ℤ) → 0 < a j) →
    a (N : ℤ) = a ((N : ℤ) - 1) →
    p (-1 : ℤ) = 0 →
    p 0 = 1 →
    (∀ j : ℤ, 0 ≤ j → j < (N : ℤ) →
      C (a (j + 1)) * p (j + 1) =
        X * p j - C (a j) * p (j - 1)) ∧
    (∀ j : ℤ, 0 ≤ j → j < (N : ℤ) →
      let Y : ℤ → (Fin 2 → Polynomial ℝ) :=
        fun k i => if i = (0 : Fin 2) then p k else p (k - 1)
      let T : ℤ → Matrix (Fin 2) (Fin 2) (Polynomial ℝ) :=
        fun k i l =>
          if i = (0 : Fin 2) then
            if l = (0 : Fin 2) then C (1 / a (k + 1)) * X
            else -C (a k / a (k + 1))
          else if l = (0 : Fin 2) then 1 else 0
      Y (j + 1) = Matrix.mulVec (T j) (Y j))

end MathlibPlus.Open.Research
