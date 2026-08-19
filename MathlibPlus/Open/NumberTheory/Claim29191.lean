import Mathlib

namespace MathlibPlus.Open.NumberTheory

/-- Claim 29191: the product-action order equation has the stated 2-adic
consequences when the odd factor is the order of A. -/
def productActionExponent_claim29191 : Prop :=
  ∀ (a m d : ℕ),
    0 < a →
    ¬ 2 ∣ a →
    2 ≤ d →
    8 * a = m ^ d →
      padicValNat 2 (8 * a) = 3 ∧
      d ∣ 3 ∧
      d = 3 ∧
      padicValNat 2 m = 1 ∧
      m % 4 = 2

end MathlibPlus.Open.NumberTheory
