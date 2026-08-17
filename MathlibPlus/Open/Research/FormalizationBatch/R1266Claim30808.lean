import Mathlib

namespace MathlibPlus.Open.Research.R1266

noncomputable section
open Polynomial

abbrev RationalFunction := RatFunc ℚ

def rationalX : RationalFunction := RatFunc.X

def J (d : ℕ) : RationalFunction :=
  (1 + rationalX)^d - rationalX^d - (d : RationalFunction) * rationalX^(d - 1)

def C0 (a b : ℕ) : RationalFunction :=
  (1 + rationalX)^(a + b) +
    (1 + rationalX)^a * rationalX^(b + 1) + rationalX^(a + b + 2)

def C1 (a b : ℕ) : RationalFunction :=
  J b * ((1 + rationalX)^a + rationalX^(a + 1)) +
    (1 + rationalX)^(a + b) + (1 + rationalX)^a * rationalX^(b + 1) -
      rationalX^(a + b + 1) - (a + 1 : RationalFunction) * rationalX^(a + b)

def P (a b : ℕ) : Polynomial RationalFunction :=
  Polynomial.C (C0 a b) + Polynomial.C (C1 a b) * Polynomial.X +
    Polynomial.C (J a * J b) * Polynomial.X^2

def rootBalanced (a b : ℕ) : Prop :=
  2 ≤ a ∧ 2 ≤ b ∧ a ≤ 2 * b - 1

def claim30808 : Prop :=
  (∀ a b : ℕ, rootBalanced a b →
    (P a b).natDegree = 2 ∧ Irreducible (P a b)) ∧
  (∀ a b a' b' : ℕ,
    rootBalanced a b → rootBalanced a' b' →
      (a, b) ≠ (a', b') → ¬ Associated (P a b) (P a' b'))

end
end MathlibPlus.Open.Research.R1266
