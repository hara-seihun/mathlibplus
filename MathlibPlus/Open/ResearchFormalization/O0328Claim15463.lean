import MathlibPlus.Open.Analysis.Claim11235_11240_11241
import MathlibPlus.Open.ResearchFormalization.O0328LogDerivativeAndFibers

open Set

namespace MathlibPlus.Open.ResearchFormalization.O0328Claim15463

noncomputable section

/-- Real-entire even functions, with the real type and the intrinsic
maximum-modulus order bound used for the compact-source multiplier. -/
def realEntireEvenOrderAtMostOne (F : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ F Set.univ ∧
    Differentiable ℂ F ∧
      (∀ z : ℂ, F (-z) = F z) ∧
        (∀ z : ℂ, F (starRingEnd ℂ z) = starRingEnd ℂ (F z)) ∧
          (∀ x : ℝ, (F (x : ℂ)).im = 0) ∧
            MathlibPlus.Open.Analysis.entireOrder F ≤ ENNReal.ofReal 1

/-- Every source in the reviewed center-flat compact class has the stated
real-entire, even, order-at-most-one centered multiplier. -/
def claim15463 : Prop :=
  ∀ (a R : ℝ),
    0 < a →
      a < R →
        ∀ q : ℝ → ℝ,
          q ∈
              MathlibPlus.Open.Analysis.CenterFlatCompactSourceClaim15459.centerFlatSourceClass
                a R →
            realEntireEvenOrderAtMostOne
              (MathlibPlus.Open.ResearchFormalization.O0328LogDerivativeAndFibers.centeredMultiplier q)

end

end MathlibPlus.Open.ResearchFormalization.O0328Claim15463
