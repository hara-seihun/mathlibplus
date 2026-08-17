import MathlibPlus.Open.ResearchFormalizationBatch_01a000eb669c70a2a7aa12653a5c13d3

namespace MathlibPlus.Open.ResearchFormalization.R0960Claim27625

open MathlibPlus.Open.ResearchFormalizationBatch_01a000eb669c70a2a7aa12653a5c13d3

noncomputable section

/-- The two one-sided tensor derivations whose sum is tensorD. -/
def leftTensorDerivation : H →ₗ[ℚ] H :=
  TensorProduct.map planarDerivation (LinearMap.id : F →ₗ[ℚ] F)

def rightTensorDerivation : H →ₗ[ℚ] H :=
  TensorProduct.map (LinearMap.id : F →ₗ[ℚ] F) planarDerivation

/-- The bidegree component recurrence in Claim 27625. -/
def interiorSchurRecurrence_claim27625 : Prop :=
  ∀ (w : ℕ) (g : H) (gPart : ℕ → H),
    (g = ∑ p ∈ Finset.Icc 1 (w - 1), gPart p) ∧
    (∀ p : ℕ, p ∈ Finset.Icc 1 (w - 1) →
      gPart p ∈ Submodule.span ℚ {h : H |
        ∃ x y : PlanarMagma, PlanarMagma.wt x = p ∧
          PlanarMagma.wt y = w - p ∧
          h = TensorProduct.tmul ℚ (basis x) (basis y)}) ∧
    (tensorE - tensorD.comp tensorD) g = 0 ∧
    gPart 0 = 0 ∧ gPart w = 0 →
    ∀ r : ℕ, 2 ≤ r → r ≤ w →
      leftTensorDerivation (leftTensorDerivation (gPart (r - 2))) +
          2 • leftTensorDerivation (rightTensorDerivation (gPart (r - 1))) +
          rightTensorDerivation (rightTensorDerivation (gPart r)) = 0

end

end MathlibPlus.Open.ResearchFormalization.R0960Claim27625
