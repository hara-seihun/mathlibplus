import Mathlib

namespace MathlibPlus.Open.GraphTheory.Q0090

/-- Claim 16564, with the P1 outer-shell condition expanded as the
pairwise-coprime three-factor product specified by the source packet. -/
def claim16564 : Prop :=
  ∀ (H₁ H₂ H₃ : Type*) [Group H₁] [Group H₂] [Group H₃]
    [Finite H₁] [Finite H₂] [Finite H₃],
    Nat.card (H₁ × H₂ × H₃) ≤ 47 →
    Nat.Coprime (Nat.card H₁) (Nat.card H₂) →
    Nat.Coprime (Nat.card H₁) (Nat.card H₃) →
    Nat.Coprime (Nat.card H₂) (Nat.card H₃) →
    (∀ (S T : Set (H₁ × H₂ × H₃)),
      (∀ x, x ∈ S ↔ x⁻¹ ∈ S) →
      1 ∉ S →
      (∀ x, x ∈ T ↔ x⁻¹ ∈ T) →
      1 ∉ T →
      Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) →
      ∃ f : (H₁ × H₂ × H₃) ≃* (H₁ × H₂ × H₃), f '' S = T)

end MathlibPlus.Open.GraphTheory.Q0090
