import MathlibPlus.Open.ResearchFormalization.R0474Claim21849

open Asymptotics Filter

namespace MathlibPlus.Open.ResearchFormalization.R0474

noncomputable section

/-- Claim 21863: a single absolute polynomial-loss constant gives the joint
positive `(x,t)` Fock bound on the explicit complex feature. -/
def claim21863_jointPositiveFockBound : Prop :=
  ∃ C₀ : ℝ,
    0 ≤ C₀ ∧
      ∀ x t : ℝ, 2 ≤ x → 2 ≤ t →
        ∀ z : ℂ, ‖z - (t : ℂ)‖ ≤ 1 →
          isFeatureVector_21850 (complexFeature_21850 x z) ∧
            featureNorm_21850 (complexFeature_21850 x z) ≤
              Real.rpow (x + t) C₀ *
                Real.exp
                  (x / 2 +
                    ((3 / 2 : ℝ) * Real.rpow 4 (1 / 3 : ℝ)) *
                      Real.rpow x (1 / 3 : ℝ) *
                        Real.rpow (t + 1) (2 / 3 : ℝ))

end

end MathlibPlus.Open.ResearchFormalization.R0474
