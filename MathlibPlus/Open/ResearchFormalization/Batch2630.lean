import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch2630

noncomputable def splitSum (S B : ℂ → ℂ) : ℂ → ℂ :=
  fun z => S z + B z

noncomputable def projectiveRatio (S B : ℂ → ℂ) : ℂ → ℂ :=
  fun z => -B z / S z

noncomputable def splitWronskian (S B : ℂ → ℂ) : ℂ → ℂ :=
  fun z => S z * deriv B z - deriv S z * B z

noncomputable def stokesGraph (S B : ℂ → ℂ) : Set ℂ :=
  {z | ‖projectiveRatio S B z‖ = 1}

/-- Projective split identities and the double-zero discriminant. -/
def claim_42952 : Prop :=
  ∀ (S B : ℂ → ℂ),
    Differentiable ℂ S → Differentiable ℂ B →
    (∀ z : ℂ, ¬(S z = 0 ∧ B z = 0)) →
    ∀ z : ℂ, S z ≠ 0 →
      ((B z ≠ 0 →
          deriv (projectiveRatio S B) z / projectiveRatio S B z =
              (deriv B z / B z - deriv S z / S z) ∧
            deriv (projectiveRatio S B) z / projectiveRatio S B z =
              splitWronskian S B z / (S z * B z)) ∧
        (splitSum S B z = 0 ↔ projectiveRatio S B z = 1) ∧
        (splitSum S B z = 0 →
          deriv (splitSum S B) z = splitWronskian S B z / S z) ∧
        ((splitSum S B z = 0 ∧ deriv (splitSum S B) z = 0) ↔
          (projectiveRatio S B z = 1 ∧ splitWronskian S B z = 0)))

end MathlibPlus.Open.ResearchFormalization.Batch2630
