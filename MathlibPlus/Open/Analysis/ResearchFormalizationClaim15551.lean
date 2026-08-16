import Mathlib
import MathlibPlus.Open.Analysis.ResearchFormalizationClaim15557

open scoped BigOperators
open MeasureTheory Set

namespace MathlibPlus.Open.Analysis.ResearchFormalizationClaim15551

noncomputable section

/-- The exact archimedean density in the completed mixed carrier. -/
noncomputable def kappa (t : ℝ) : ℝ :=
  t * ((Real.exp (2 * t) - 1)⁻¹ - Real.exp t)

/-- Claim 15551: for the exact locally finite mixed carrier, a real-valued
analytic multiplier has the continuous-density sign and the prime-atom sign
collision. -/
def completedMixedCarrierSign_claim15551 : Prop :=
  ∀ M : ℂ → ℂ,
    (AnalyticOnNhd ℂ M
        MathlibPlus.Open.Analysis.ResearchFormalizationClaim15557.rightHalfPlane ∧
      (∀ t : ℝ, 0 < t → (M (t : ℂ)).im = 0)) →
    (∃ ν : Measure ℝ,
      MathlibPlus.Open.Analysis.ResearchFormalizationClaim15557.exactCompletedMixedCarrier
        M ν) →
      (∀ t : ℝ, Real.log 2 ≤ t → kappa t < 0) ∧
      (∀ t : ℝ, Real.log 2 ≤ t →
        MathlibPlus.Open.Analysis.ResearchFormalizationClaim15557.multiplierRealPart M t ≤ 0) ∧
      (∀ p : ℕ, Nat.Prime p →
        MathlibPlus.Open.Analysis.ResearchFormalizationClaim15557.completedMixedAtom M p =
            (Real.log (p : ℝ)) ^ 2 *
              MathlibPlus.Open.Analysis.ResearchFormalizationClaim15557.multiplierRealPart
                M (Real.log (p : ℝ)) ∧
          0 ≤ (Real.log (p : ℝ)) ^ 2 *
            MathlibPlus.Open.Analysis.ResearchFormalizationClaim15557.multiplierRealPart
              M (Real.log (p : ℝ)) ∧
          MathlibPlus.Open.Analysis.ResearchFormalizationClaim15557.multiplierRealPart
              M (Real.log (p : ℝ)) = 0)

end

end MathlibPlus.Open.Analysis.ResearchFormalizationClaim15551
