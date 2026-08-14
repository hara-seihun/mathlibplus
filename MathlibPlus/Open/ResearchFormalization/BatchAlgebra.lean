import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch.Algebra

/-- A divisibility-greatest common divisor, which is the UFD notion used by the
one-marker primitive-content split. -/
def IsDivisibilityGcd {R : Type*} [CommMonoidWithZero R]
    (h a b : R) : Prop :=
  h ∣ a ∧ h ∣ b ∧ ∀ d : R, d ∣ a → d ∣ b → d ∣ h

/-- Exact one-marker primitive-content descent over the coefficient UFD. -/
def claim_27595 {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] : Prop :=
  ∀ (a b h a' b' : R) (F : Polynomial R),
    F = Polynomial.C b + Polynomial.C a * Polynomial.X →
    (∀ r : R, F ≠ Polynomial.C r) →
    IsDivisibilityGcd h a b →
    h * a' = a →
    h * b' = b →
    a' ≠ 0 ∧
      Polynomial.IsPrimitive (Polynomial.C b' + Polynomial.C a' * Polynomial.X) ∧
      Irreducible (Polynomial.C b' + Polynomial.C a' * Polynomial.X)

end MathlibPlus.Open.ResearchFormalizationBatch.Algebra
