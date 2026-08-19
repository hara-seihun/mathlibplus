import Mathlib

namespace MathlibPlus.Open.Analysis.Claim44756

open _root_.MeasureTheory

/-- Exact normalized nonnegative-kernel average bound, including its
uniformly-negative-field consequence. -/
def claim44756_kernelAverageBound : Prop :=
  ∀ (K F : ℝ → ℝ) (S : Set ℝ),
    (∀ w : ℝ, 0 ≤ K w) →
    _root_.MeasureTheory.Integrable K →
    (∫ w : ℝ, K w ∂(_root_.MeasureTheory.MeasureSpace.volume)) = 1 →
    _root_.MeasureTheory.Integrable (fun w : ℝ => K w * F w) →
    S.Nonempty →
    (∀ᵐ w : ℝ ∂(_root_.MeasureTheory.MeasureSpace.volume), K w ≠ 0 → w ∈ S) →
    (∃ C : ℝ, ∀ w : ℝ, w ∈ S → F w ≤ C) →
    (∫ w : ℝ, K w * F w ∂(_root_.MeasureTheory.MeasureSpace.volume)) ≤ sSup (F '' S) ∧
      (∀ δ : ℝ, 0 < δ →
        (∀ w : ℝ, w ∈ S → F w ≤ -δ) →
        ¬ (0 < ∫ w : ℝ, K w * F w ∂(_root_.MeasureTheory.MeasureSpace.volume)))

end MathlibPlus.Open.Analysis.Claim44756
