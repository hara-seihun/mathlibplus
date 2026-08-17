import Mathlib

open scoped Interval
open MeasureTheory
open Set

namespace MathlibPlus.Open.ResearchFormalizationBatch.C0158Claim2465

noncomputable section

/-- The logarithmic profile/kernel correspondence, including its inverse and
zero-moment transport. -/
def claim2465_converseRealizationOfEndpointShapes : Prop :=
  ∀ (B : ℝ),
    1 < B → B < 2 →
      (∀ (φ : ℝ → ℝ),
        ContDiff ℝ ⊤ φ →
        HasCompactSupport φ →
        Function.support φ ⊆ Ioo (1 : ℝ) B →
          ∃! (k : ℝ → ℝ),
            ContDiff ℝ ⊤ k ∧
              HasCompactSupport k ∧
              Function.support k ⊆ Ioo (0 : ℝ) (Real.log B) ∧
              (∀ x : ℝ,
                k x = Real.exp (x / 2) * φ (Real.exp x)) ∧
              ((∫ u in (1 : ℝ)..B, φ u) = 0 ↔
                (∫ x in (0 : ℝ)..Real.log B,
                  Real.exp (x / 2) * k x) = 0)) ∧
      (∀ (k : ℝ → ℝ),
        ContDiff ℝ ⊤ k →
        HasCompactSupport k →
        Function.support k ⊆ Ioo (0 : ℝ) (Real.log B) →
          ∃! (φ : ℝ → ℝ),
            ContDiff ℝ ⊤ φ ∧
              HasCompactSupport φ ∧
              Function.support φ ⊆ Ioo (1 : ℝ) B ∧
              (∀ u : ℝ,
                0 < u →
                  φ u = Real.rpow u (-(1 / 2 : ℝ)) * k (Real.log u)) ∧
              (∀ x : ℝ,
                k x = Real.exp (x / 2) * φ (Real.exp x)) ∧
              ((∫ u in (1 : ℝ)..B, φ u) = 0 ↔
                (∫ x in (0 : ℝ)..Real.log B,
                  Real.exp (x / 2) * k x) = 0))

end

end MathlibPlus.Open.ResearchFormalizationBatch.C0158Claim2465
