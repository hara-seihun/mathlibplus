import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatchO0325

/-- The projective ratio of the shadow channel to the distinguished channel. -/
noncomputable def projectiveRatio (S B : ℂ → ℂ) (z : ℂ) : ℂ :=
  -B z / S z

/-- The coefficient of the logarithmic differential of the projective ratio. -/
noncomputable def projectiveLogDerivative (S B : ℂ → ℂ) (z : ℂ) : ℂ :=
  deriv (fun w : ℂ => projectiveRatio S B w) z /
    projectiveRatio S B z

/-- Claim 15404: a common nowhere-zero multiplier cancels from both the
projective ratio and its logarithmic derivative, whereas a multiplier on the
S channel contributes with the opposite sign to the relative logarithmic
charge. -/
def claim15404_commonAndShadowOnlyMultipliers : Prop :=
  ∀ S B g h : ℂ → ℂ,
    Differentiable ℂ S → Differentiable ℂ B →
    Differentiable ℂ g → Differentiable ℂ h →
    (∀ z : ℂ, g z ≠ 0) → (∀ z : ℂ, h z ≠ 0) →
      (∀ z : ℂ,
        projectiveRatio (fun w => g w * S w) (fun w => g w * B w) z =
          projectiveRatio S B z) ∧
      (∀ z : ℂ, S z ≠ 0 → B z ≠ 0 →
        projectiveLogDerivative
            (fun w => g w * S w) (fun w => g w * B w) z =
          projectiveLogDerivative S B z) ∧
      (∀ z : ℂ, S z ≠ 0 → B z ≠ 0 →
        projectiveLogDerivative (fun w => h w * S w) B z =
          projectiveLogDerivative S B z - deriv h z / h z)

end MathlibPlus.Open.Research.FormalizationBatchO0325
