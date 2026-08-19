import Mathlib

namespace MathlibPlus.Open.Algebra

/-- Claim 11663: a zero rational generic fibre annihilates the unit by a
nonzero integer. -/
def emptyGenericFiberAnnihilatesUnit_claim11663 : Prop :=
  ∀ (A : Type*) [CommRing A] [Algebra ℤ A],
    (∀ x : TensorProduct ℤ A ℚ, x = 0) →
      ∃ n : ℤ, n ≠ 0 ∧ n • (1 : A) = 0

end MathlibPlus.Open.Algebra
