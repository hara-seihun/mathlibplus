import MathlibPlus.Open.ResearchFormalizationBatch_01a000eb669c70a2a7aa12653a5c13d3

namespace MathlibPlus.Open.ResearchFormalization.R0960Claim27624

open MathlibPlus.Open.ResearchFormalizationBatch_01a000eb669c70a2a7aa12653a5c13d3

noncomputable section

/-- The subspace of tensors supported on the indicated pair of magma weights. -/
def homogeneousTensorSubspace (p q : ℕ) : Submodule ℚ H :=
  Submodule.span ℚ {h : H |
    ∃ x y : PlanarMagma, PlanarMagma.wt x = p ∧
      PlanarMagma.wt y = q ∧ h = TensorProduct.tmul ℚ (basis x) (basis y)}

/-- The two extreme target bidegrees after applying the root-forgetting
    correction to a total-weight `w` component. -/
def extremeTargetSubspace (w : ℕ) : Submodule ℚ H :=
  homogeneousTensorSubspace 1 (w + 1) ⊔
    homogeneousTensorSubspace (w + 1) 1

/-- Claim 27624: if a tensor is decomposed into the indicated homogeneous
    bidegrees, tensorE has support only in the two extreme target bidegrees. -/
def extremeBidegreeSupportOfE_claim27624 : Prop :=
  ∀ (w : ℕ) (g : H) (gPart : ℕ → H),
    (g = ∑ p ∈ Finset.Icc 1 (w - 1), gPart p) ∧
    (∀ p : ℕ, p ∈ Finset.Icc 1 (w - 1) →
      gPart p ∈ homogeneousTensorSubspace p (w - p)) →
      tensorE g ∈ extremeTargetSubspace w

end

end MathlibPlus.Open.ResearchFormalization.R0960Claim27624
