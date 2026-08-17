import MathlibPlus.Open.Research.SomlaiBoundaryDefect

namespace MathlibPlus.Open.ResearchFormalization.Somlai6479

open scoped TensorProduct
open MathlibPlus.Open.Research.Somlai

noncomputable section

/-- Claim 6479: the explicit Somlai group-algebra construction records the
relation module, augmentation ideal, first moment, restricted kernel, and the
boundary quotient without replacing any of them by an interface parameter. -/
def relationModuleFirstMomentDefect_claim6479 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    (∀ L : SomlaiLabel p, somlaiDirection p L ≠ 0) ∧
    relationModule p =
      Submodule.span (ZMod p) {z |
        ∃ L : SomlaiLabel p, ∃ u : SomlaiV p,
          u ∈ coefficientLine p L ∧ ∃ r : GroupAlgebra p,
            z = u ⊗ₜ[ZMod p]
              ((tau p (somlaiDirection p L) - 1) * r)} ∧
    augmentationIdeal p =
      RingHom.ker (augmentation p).toRingHom ∧
    (∀ (v : SomlaiV p) (x : SomlaiB p),
      firstMoment p (v ⊗ₜ[ZMod p] tau p x) =
        TensorProduct.tmul (ZMod p) v x) ∧
    momentKernelInC p = relationModule p ⊓ (firstMoment p).ker ∧
    augmentationProductInKernel p =
      Submodule.comap (momentKernelInC p).subtype (augmentationProduct p) ∧
    boundaryDefect p =
      Module.finrank (ZMod p)
        (momentKernelInC p ⧸ augmentationProductInKernel p)

end

end MathlibPlus.Open.ResearchFormalization.Somlai6479
