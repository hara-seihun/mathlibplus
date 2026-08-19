import MathlibPlus.Open.ResearchFormalization.C7AffineSectionTransporter

namespace MathlibPlus.Open.ResearchFormalization.R1210AffineSectionTransporter32278

open MathlibPlus.Open.ResearchFormalization.C7AffineSectionTransporter

noncomputable section

/-- Claim 32278: the affine section transporter on `E(C₇²,3)` has the
literal three-section formula, is an automorphism, preserves empty and full
kernel sections, and maps `B` and `3B` to their affine images. -/
def claim32278 : Prop :=
  ∀ (B C : Finset C7Vector) (L : C7Vector ≃ₗ[ZMod 7] C7Vector)
    (c : C7Vector),
    C = affineImage L c B →
      (∀ a : C7Vector,
        sectionTransport L c (a, (0 : Fin 3)) = (L a, (0 : Fin 3))) ∧
      (∀ a : C7Vector,
        sectionTransport L c (a, (1 : Fin 3)) = (L a + c, (1 : Fin 3))) ∧
      (∀ a : C7Vector,
        sectionTransport L c (a, (2 : Fin 3)) =
          (L a + 3 • c, (2 : Fin 3))) ∧
      extensionAutomorphism (sectionTransport L c) ∧
      Set.image (sectionTransport L c) (kernelSection ∅ 0) =
        kernelSection ∅ 0 ∧
      Set.image (sectionTransport L c) (kernelSection Finset.univ 0) =
        kernelSection Finset.univ 0 ∧
      Set.image (sectionTransport L c) (kernelSection B 1) =
        kernelSection C 1 ∧
      Set.image (sectionTransport L c) (kernelSection (tripleImage B) 2) =
        kernelSection (tripleImage C) 2

end

end MathlibPlus.Open.ResearchFormalization.R1210AffineSectionTransporter32278
