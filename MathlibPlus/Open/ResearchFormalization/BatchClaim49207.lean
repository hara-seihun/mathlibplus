import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchClaim49207

open scoped BigOperators

/-- The coefficient of degree `n` in a finite coefficient list, extended by zero. -/
def coefficient (p : List ℕ) (n : ℕ) : ℕ := p.getD n 0

/-- Cauchy convolution of two finite coefficient lists, extended by zero. -/
def coefficientConvolution (p q : List ℕ) (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1))
    (fun i => coefficient p i * coefficient q (n - i))

/-- Weak unimodality with a specified mode. -/
def unimodalAt (f : ℕ → ℕ) (m : ℕ) : Prop :=
  (∀ ⦃i j : ℕ⦄, i ≤ j → j ≤ m → f i ≤ f j) ∧
    (∀ ⦃i j : ℕ⦄, m ≤ i → i ≤ j → f j ≤ f i)

/-- A specified mode is the unique strict maximizer. -/
def uniqueModeAt (f : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ n, n ≠ m → f n < f m

def p4Coefficients : List ℕ := [1, 4, 3]

def order26Coefficients : List ℕ :=
  [1, 26, 300, 2040, 9142, 28551, 63933, 103736, 121376, 100144,
    55499, 18683, 2979, 51, 1]

def productCoefficients : List ℕ :=
  [1, 30, 407, 3318, 18202, 71239, 205563, 445121, 728119, 896856,
    820203, 541111, 244208, 68016, 9142, 157, 3]

/-- Exact coefficient data for the named `P₄`/order-26 product. -/
def claim49207 : Prop :=
  (∀ n, coefficientConvolution p4Coefficients order26Coefficients n =
    coefficient productCoefficients n) ∧
    unimodalAt (coefficient productCoefficients) 9 ∧
    uniqueModeAt (coefficient productCoefficients) 9 ∧
    coefficient productCoefficients 15 * coefficient productCoefficients 15 <
      coefficient productCoefficients 14 * coefficient productCoefficients 16

end MathlibPlus.Open.ResearchFormalization.BatchClaim49207
