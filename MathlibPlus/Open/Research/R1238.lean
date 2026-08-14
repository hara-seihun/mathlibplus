import Mathlib

namespace MathlibPlus.Open.Research.R1238

open Polynomial

noncomputable section

def spiderOrder (a b : Nat) : Nat := 1 + a + 2 * b

def spiderDegree (a b : Nat) : Nat := a + b

def spiderL : Polynomial ℚ := 1 + X

def spiderQ : Polynomial ℚ := X ^ 2 + X + 1

def spiderH (a b : Nat) : Polynomial ℚ :=
  spiderL ^ (a - 1) * spiderQ ^ b

def shortLeafB (a b : Nat) : Polynomial ℚ :=
  spiderH a b + X ^ (spiderOrder a b - 1) * spiderL

def shortLeafA (a b : Nat) : Polynomial ℚ :=
  (X + 2) * spiderH a b -
    X ^ (spiderOrder a b - 3) *
      (X ^ 2 + C ((spiderDegree a b + 1 : Nat) : ℚ) * X +
        C ((spiderDegree a b - 1 : Nat) : ℚ))

def shortLeafFactor (a b : Nat) : Polynomial (Polynomial ℚ) :=
  C (shortLeafB a b) + X * C (shortLeafA a b)

def claim30454 : Prop :=
  ∀ a b : Nat, 1 ≤ a → a + b = 2 →
    ((a = 2 ∧ b = 0) ∨ (a = 1 ∧ b = 1)) ∧
      ((a = 2 ∧ b = 0 → shortLeafA a b = 1) ∧
        (a = 1 ∧ b = 1 → shortLeafA a b = 2 * spiderL) ∧
        (a = 1 ∧ b = 1 → eval (-1) (shortLeafB a b) = 1)) ∧
      ((a = 2 ∧ b = 0 → IsCoprime (shortLeafA a b) (shortLeafB a b)) ∧
        (a = 1 ∧ b = 1 → IsCoprime (shortLeafA a b) (shortLeafB a b)))

def claim30455 : Prop :=
  ∀ a b : Nat, 1 ≤ a → 3 ≤ spiderOrder a b →
    Polynomial.IsPrimitive (shortLeafFactor a b) ∧
      Irreducible (shortLeafFactor a b)

end

end MathlibPlus.Open.Research.R1238
