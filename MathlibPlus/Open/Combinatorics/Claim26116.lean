import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- Faithful registry node for unequal-total double-spider derivative
injectivity.  Double-spider structure, unspecialized p₁ derivative, and
isomorphism are explicit source interfaces. -/
def unequalDerivativeInjectivity_claim26116 : Prop :=
  ∀ (DoubleSpider DerivativeTarget : Type*)
    (total smallerSideLegs : DoubleSpider → ℕ)
    (p₁Derivative : DoubleSpider → DerivativeTarget)
    (Isomorphic : DoubleSpider → DoubleSpider → Prop)
    (A B : DoubleSpider),
    total A ≠ total B →
    3 ≤ smallerSideLegs A →
    3 ≤ smallerSideLegs B →
    p₁Derivative A = p₁Derivative B →
    Isomorphic A B

end MathlibPlus.Open.Combinatorics
