import MathlibPlus.Open.FormalizationBatch.K0110

namespace MathlibPlus.Open.ResearchFormalization.K0110.Claim8660

open MathlibPlus.Open.FormalizationBatch.K0110

noncomputable section

/-- The canonical whitened `N`-slope. -/
def whitenedNSlope_claim8660 {n : ℕ}
    (N₀ S_N : Matrix (Fin n) (Fin n) ℝ) (hN₀ : N₀.PosDef) :
    Matrix (Fin n) (Fin n) ℝ :=
  canonicalInverseSqrt N₀ hN₀ * S_N * canonicalInverseSqrt N₀ hN₀

/-- The canonical whitened `M`-slope. -/
def whitenedMSlope_claim8660 {n : ℕ}
    (M₀ S_M : Matrix (Fin n) (Fin n) ℝ) (hM₀ : M₀.PosDef) :
    Matrix (Fin n) (Fin n) ℝ :=
  canonicalInverseSqrt M₀ hM₀ * S_M * canonicalInverseSqrt M₀ hM₀

/-- The maximum operator-2 norm of the two canonical whitened slopes. -/
def canonicalWhitenedSlopeNorm_claim8660 {n : ℕ}
    (N₀ M₀ S_N S_M : Matrix (Fin n) (Fin n) ℝ)
    (hN₀ : N₀.PosDef) (hM₀ : M₀.PosDef) : ℝ :=
  max
    (operatorTwoNorm (whitenedNSlope_claim8660 N₀ S_N hN₀))
    (operatorTwoNorm (whitenedMSlope_claim8660 M₀ S_M hM₀))

end

end MathlibPlus.Open.ResearchFormalization.K0110.Claim8660
