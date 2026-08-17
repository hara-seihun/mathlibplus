import Mathlib
import MathlibPlus.Open.Research.Q12CIBatch

namespace MathlibPlus.Open.NewResearch2.R1086Claim28746

noncomputable section

abbrev FourColors := Fin 4

def colorPreservingDirectedIso
    {G : Type*} [Group G]
    (c d : G → FourColors) (e : Equiv G G) : Prop :=
  e 1 = 1 ∧
    ∀ (i : FourColors) (x y : G),
      (c (x⁻¹ * y) = i ↔
        d ((e x)⁻¹ * e y) = i)

def claim28746_allFourColorDirectedCayleyStructuresAreCI : Prop :=
  ∀ {G : Type*} [Group G] [Fintype G]
    (a b : G),
    MathlibPlus.Open.Research.Q12.isQ12Presentation a b →
      ∀ (c d : G → FourColors),
        c 1 = 0 →
          d 1 = 0 →
            ∀ e : Equiv G G,
              colorPreservingDirectedIso c d e →
                ∃ φ : G ≃* G,
                  ∀ h : G, c h = d (φ h)

end

end MathlibPlus.Open.NewResearch2.R1086Claim28746
