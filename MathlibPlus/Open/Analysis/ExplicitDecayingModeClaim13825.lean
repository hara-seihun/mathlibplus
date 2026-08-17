import MathlibPlus.Open.Analysis.ModeTransport

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- Claim 13825: the lower-endpoint mode and its Hedenmalm gauge at a
bilateral-Laplace zero. -/
def explicitDecayingModeAtBilateralLaplaceZero_claim13825 : Prop :=
  ∀ (h φ : ℝ → ℝ) (spectral : ℂ),
    rapidlyDecreasing h →
    (∀ x : ℝ, h (-x) = h x) →
    (∀ x : ℝ, h x = Real.exp (-(φ x))) →
    MeasureTheory.Integrable
      (fun t : ℝ => Complex.exp (spectral * (t : ℂ)) * (h t : ℂ)) →
    bilateralLaplace h spectral = 0 →
    ∀ x : ℝ,
      decayingMode h spectral x =
          Complex.exp (-spectral * (x : ℂ)) *
            (∫ t : ℝ in Set.Iic x,
              Complex.exp (spectral * (t : ℂ)) * (h t : ℂ)) ∧
        gaugedMode h φ spectral x =
          Complex.exp (((φ x : ℂ) + spectral * (x : ℂ)) / 2) *
            decayingMode h spectral x

end

end MathlibPlus.Open.Analysis
