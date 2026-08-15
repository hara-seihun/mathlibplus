import Mathlib

namespace MathlibPlus.Open.Formalization.TriangularExactness

noncomputable section

/-- Claim 60022: a well-founded unitriangular family gives exactness. -/
def claim60022 : Prop :=
  ∀ (R : Type*) [CommRing R]
    (I : Type*) [LinearOrder I] [IsWellFounded I (· < ·)]
    (C1 C3 : Type*) [AddCommGroup C1] [AddCommGroup C3]
      [Module R C1] [Module R C3]
    (d₁ : C1 →ₗ[R] I →₀ R)
    (d₂ : (I →₀ R) →ₗ[R] C3),
    (∀ x : C1, d₂ (d₁ x) = 0) →
      (∀ i : I, ∃ xi : C1,
        (d₁ xi) i = 1 ∧
          ∀ j : I, i < j → (d₁ xi) j = 0) →
        (∀ y : I →₀ R, ∃ x : C1, d₁ x = y) ∧
          (∀ y : I →₀ R,
            d₂ y = 0 ↔ ∃ x : C1, d₁ x = y)

end

end MathlibPlus.Open.Formalization.TriangularExactness
