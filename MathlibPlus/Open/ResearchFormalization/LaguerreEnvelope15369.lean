import Mathlib
import MathlibPlus.Open.ResearchFormalization.LaguerreGeneratingFunction15360

open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization.LaguerreEnvelope15369

noncomputable section

/-- The truncated exponential counterfeit used by the envelope obstruction. -/
def truncatedExponential (δ T t : ℝ) : ℝ :=
  if T ≤ t then Real.exp (-δ * t) else 0

/-- The Laguerre transform of the truncated exponential. -/
noncomputable def truncatedExponentialLaguerreTransform
    (δ T : ℝ) (d : ℕ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ),
    truncatedExponential δ T t *
      MathlibPlus.Open.ResearchFormalization.LaguerreGeneratingFunction15360.laguerreTwo d t

/-- Claim 15369: every eventually positive envelope with subexponential
logarithmic decay admits a fixed truncated exponential whose Laguerre
transforms grow exponentially. -/
def allSubexponentialEnvelopes_claim15369 : Prop :=
  ∀ E : ℝ → ℝ,
    (∀ᶠ t in atTop, 0 < E t) ∧
      Tendsto (fun t : ℝ => -Real.log (E t) / t) atTop (𝓝 0) →
    ∃ δ T : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ 0 < T ∧
      (∀ t : ℝ, 0 ≤ t → truncatedExponential δ T t ≤ E t) ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ d in atTop,
          c * ((1 - δ) / δ) ^ d ≤
            |truncatedExponentialLaguerreTransform δ T d|

end

end MathlibPlus.Open.ResearchFormalization.LaguerreEnvelope15369
