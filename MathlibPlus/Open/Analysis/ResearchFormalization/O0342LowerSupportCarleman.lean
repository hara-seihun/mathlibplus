import Mathlib

open scoped BigOperators Topology
open Filter MeasureTheory Set

namespace MathlibPlus.Open.Analysis.ResearchFormalizationO0342

noncomputable section

/-- The dyadic weighted variation `A_j`, with the argument representing `|μ|`. -/
noncomputable def dyadicWeightedVariation (variation : Measure ℝ) (j : ℕ) : ℝ :=
  ∫ α : ℝ, Real.rpow 2 (-(((j + 1 : ℕ) : ℝ) * α)) ∂variation

/-- The reciprocal Carleman term indexed by positive natural numbers. -/
noncomputable def dyadicCarlemanTerm (variation : Measure ℝ)
    (j : {j : ℕ // 1 ≤ j}) : ℝ :=
  Real.rpow (dyadicWeightedVariation variation (2 * j.1))
    (-(1 : ℝ) / (2 * (j.1 : ℝ)))

/-- The lower bound for the corresponding Carleman term. -/
noncomputable def dyadicCarlemanLowerBound (variation : Measure ℝ) (a : ℝ)
    (j : {j : ℕ // 1 ≤ j}) : ℝ :=
  (Real.rpow 2 (-a))⁻¹ *
    Real.rpow (dyadicWeightedVariation variation 0)
      (-(1 : ℝ) / (2 * (j.1 : ℝ)))

/-- Claim 15568: a lower support bound makes the dyadic Carleman series automatic.

The measure parameter is the total-variation carrier `|μ|`; its support is
therefore the support of the signed shift measure. -/
noncomputable def lowerSupportAutomaticCarleman_claim15568 : Prop :=
  ∀ (variation : Measure ℝ) (a : ℝ),
    IsLocallyFiniteMeasure variation →
    Measure.Regular variation →
    variation.support ⊆ Ici a →
    Integrable (fun α : ℝ => Real.rpow 2 (-α)) variation →
    let R : ℝ := Real.rpow 2 (-a)
    ((∀ j : ℕ,
        Integrable
          (fun α : ℝ => Real.rpow 2 (-(((j + 1 : ℕ) : ℝ) * α))) variation) ∧
      ∀ j : ℕ,
        dyadicWeightedVariation variation j ≤
          R ^ j * dyadicWeightedVariation variation 0) ∧
    (variation ≠ 0 →
      0 < R⁻¹ ∧
      0 < dyadicWeightedVariation variation 0 ∧
      (∀ j : {j : ℕ // 1 ≤ j},
        dyadicCarlemanLowerBound variation a j ≤
          dyadicCarlemanTerm variation j) ∧
      Tendsto (fun j : {j : ℕ // 1 ≤ j} =>
        dyadicCarlemanLowerBound variation a j) atTop (𝓝 R⁻¹) ∧
      ¬ Summable (fun j : {j : ℕ // 1 ≤ j} =>
        dyadicCarlemanTerm variation j))

end
end MathlibPlus.Open.Analysis.ResearchFormalizationO0342
