import Mathlib
import MathlibPlus.Open.ResearchFormalization.R0474FixedXHilbertCauchy

open Asymptotics Filter

namespace MathlibPlus.Open.ResearchFormalization.R0474

noncomputable section

/-- Fixed-parameter unit-disc growth of the explicit complex Hilbert feature,
with the same cubic-root center window and fixed-x remainder convention as the
reviewed Cauchy carrier. -/
def claim21849_fixedXFeatureGrowth : Prop :=
  ∀ x : ℝ, 0 < x →
    ∀ A : ℝ, 0 ≤ A →
      ∃ E : ℝ → ℝ,
        IsBigO atTop E
            (fun T : ℝ =>
              Real.rpow T (1 / 3 : ℝ) + Real.log T) ∧
          ∀ᶠ T : ℝ in atTop,
            ∀ t : ℝ,
              |t - T| ≤ A * Real.rpow T (2 / 3 : ℝ) →
                ∀ z : ℂ,
                  ‖z - (t : ℂ)‖ ≤ 1 →
                    isFeatureVector_21850
                        (complexFeature_21850 x z) ∧
                      featureNorm_21850 (complexFeature_21850 x z) ≤
                        Real.exp
                          ((3 / 2 : ℝ) *
                              Real.rpow x (1 / 3 : ℝ) *
                              Real.rpow T (2 / 3 : ℝ) + E T)

end

end MathlibPlus.Open.ResearchFormalization.R0474
