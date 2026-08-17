import MathlibPlus.Open.ResearchFormalizationBatch_01a0032b.CoordinateWeylGram

open scoped BigOperators
open Set

namespace MathlibPlus.Open.ResearchFormalization.Claim7578

noncomputable section

open MathlibPlus.Open.Batch_01a0032b

/-- Claim 7578: the bilateral Weyl compression equals the displayed
`2/δ` half-line integral, with the removable value retained at `δ = 0`. -/
def claim7578_exactWeylCompressionIntegral : Prop :=
  ∀ (Φ : ℝ → ℝ) (ω : ℝ) (w z : ℂ),
    superExponentialRealSource Φ →
      let δ : ℂ := z - star w
      let sigma : ℂ := z + star w
      weylCompressionIntegral Φ ω w z =
        if δ = 0 then
          2 * ∫ y : ℝ in Set.Ici 0,
            (y : ℂ) * Complex.cosh (2 * (ω : ℂ) * (y : ℂ)) *
              (y : ℂ) * sourceCorrelation Φ y sigma
        else
          (2 / δ) * ∫ y : ℝ in Set.Ici 0,
            (y : ℂ) * Complex.cosh (2 * (ω : ℂ) * (y : ℂ)) *
              Complex.sin (δ * (y : ℂ)) * sourceCorrelation Φ y sigma

end

end MathlibPlus.Open.ResearchFormalization.Claim7578
