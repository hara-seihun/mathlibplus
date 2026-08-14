import Mathlib

set_option autoImplicit false

namespace MathlibPlus.Open.R3393

/-- Digits in the displayed high-to-low convention. -/
def baseDigits (base value : ℕ) : List ℕ :=
  (Nat.digits base value).reverse

def allDigitsBelow (base : ℕ) : List ℕ → Prop
  | [] => True
  | d :: ds => d < base ∧ allDigitsBelow base ds

def digitsValid (base : ℕ) (digits : List ℕ) : Prop :=
  2 ≤ base ∧ digits ≠ [] ∧ allDigitsBelow base digits

def BaseExpansionFacts : Prop :=
  ∀ (p q r : ℕ), Nat.Prime p → Nat.Prime q → Nat.Prime r → p < q → q < r →
    let a := q - p
    let c := r - q
    let D := r - p
    p > 10 * D ^ 2 →
      a * D < p ∧ a * c < p ∧ c * D < p ∧
      baseDigits p (q * r) = [1, 2 * a + c, a * D] ∧
      digitsValid p [1, 2 * a + c, a * D] ∧
      ((c > a) →
        baseDigits q (p * r) = [1, c - a - 1, q - a * c] ∧
          digitsValid q [1, c - a - 1, q - a * c]) ∧
      ((c ≤ a) →
        baseDigits q (p * r) = [q - a + c - 1, q - a * c] ∧
          digitsValid q [q - a + c - 1, q - a * c]) ∧
      baseDigits r (p * q) = [r - a - 2 * c, c * D] ∧
      digitsValid r [r - a - 2 * c, c * D] ∧
      q * r / 2 < p ^ 2 ∧
      p * r / 2 < q ^ 2 ∧
      p * q / 2 < r ^ 2

end MathlibPlus.Open.R3393
