import Mathlib
import MathlibPlus.Open.Research.Q12CIBatch

namespace MathlibPlus.Open.ResearchFormalization.R1086Q12Claim28747

noncomputable section

/-- The identity-free four-color relation carried by a coloring of a group. -/
def fourColorPreservingIso {G : Type*} [Group G]
    (c d : G → Fin 4) (e : Equiv G G) : Prop :=
  e 1 = 1 ∧
    ∀ x y : G, x ≠ y →
      c (x⁻¹ * y) = d ((e x)⁻¹ * e y)

/-- Claim 28747: the complete four-color Q₁₂ atlas also covers every coloring
with fewer named colors, by leaving unused colors unused. -/
def allAtMostFourColorsCI_claim28747 : Prop :=
  ∀ {G : Type*} [Group G] [Fintype G]
    (a b : G),
    MathlibPlus.Open.Research.Q12.isQ12Presentation a b →
      ∀ (c d : G → Fin 4) (e : Equiv G G),
        fourColorPreservingIso c d e →
          ∃ φ : G ≃* G,
            ∀ x y : G, x ≠ y →
              c (x⁻¹ * y) = d ((φ x)⁻¹ * φ y)

end

end MathlibPlus.Open.ResearchFormalization.R1086Q12Claim28747
