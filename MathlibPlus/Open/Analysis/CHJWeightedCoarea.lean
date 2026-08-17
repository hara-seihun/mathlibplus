import Mathlib
import MathlibPlus.Open.Analysis.LayerCake

open MeasureTheory

namespace MathlibPlus.Open.Analysis.CHJWeightedCoarea

noncomputable section

/-- Claim 2018: the weighted coarea identity uses the same finite interval
components of each strict superlevel set, including the two domain traces. -/
def weightedCoareaEndpointTraces_claim2018 : Prop :=
  ∀ (ξ : ℝ) (w : ℝ → ℝ)
    (components : ℝ → Finset (ℝ × ℝ)),
    1 < ξ →
    ContDiffOn ℝ 1 w (Set.Icc (1 : ℝ) ξ) →
    (∀ u ∈ Set.Icc (1 : ℝ) ξ, 0 ≤ w u) →
    (∫ u in (1 : ℝ)..ξ, w u) = 1 →
    (∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      isLayerCakeComponentDecomposition w ξ t (components t)) →
    w 1 + w ξ / ξ +
        (∫ u in (1 : ℝ)..ξ, |deriv w u| / u) =
      ∫ t,
        (∑ p ∈ components t, (p.1⁻¹ + p.2⁻¹))
          ∂(volume.restrict (Set.Ioi (0 : ℝ)))

end
end MathlibPlus.Open.Analysis.CHJWeightedCoarea
