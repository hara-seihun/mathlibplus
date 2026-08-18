import MathlibPlus.Open.ResearchFormalization.R1441MarkedOffsetTransport

namespace MathlibPlus.Open.ResearchFormalization.R1441Claim37230

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1441MarkedOffsetTransport

/-- A normalized pure-translation profile on the matching-scalar carrier. -/
def normalizedTranslation37230 (τ : H → W) : Prop :=
  τ (0, 0) = 0

/-- The derivative subspace in row `h`, with the exact matching-scalar
semidirect-product action. -/
def derivativeSubspace37230 (τ : H → W) (h : H) : Submodule (ZMod 7) W :=
  Submodule.span (ZMod 7)
    {v | ∃ k : H,
      v = τ (hMul h k) - τ h - hScalar h (τ k)}

/-- A normalized `W`-valued cocycle for the matching-scalar action. -/
def normalizedCocycle37230 (z : H → W) : Prop :=
  z (0, 0) = 0 ∧
    ∀ h k : H, z (hMul h k) = z h + hScalar h (z k)

/-- Claim 37230: every normalized pure translation has one normalized global
cocycle shadow, with the row-wise discrepancy in the exact derivative
subspace. -/
def claim37230 : Prop :=
  ∀ τ : H → W,
    normalizedTranslation37230 τ →
      ∃ z : H → W,
        normalizedCocycle37230 z ∧
          ∀ h : H,
            τ h - z h ∈ derivativeSubspace37230 τ h

end

end MathlibPlus.Open.ResearchFormalization.R1441Claim37230
