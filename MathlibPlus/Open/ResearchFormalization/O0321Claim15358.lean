import Mathlib

open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal

namespace MathlibPlus.Open.ResearchFormalization.O0321Claim15358

noncomputable section

private def slitPlane : Set ℂ :=
  {z : ℂ | ¬ (z.im = 0 ∧ z.re ≤ 0)}

private def nonpositiveRealAxis : Set ℂ :=
  {z : ℂ | z.im = 0 ∧ z.re ≤ 0}

private def entireSquaredCarrier (E Y : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ E Set.univ ∧
    AnalyticOnNhd ℂ Y Set.univ ∧
    (∀ z : ℂ, Y z = E (z ^ 2)) ∧
    Y 0 = 1 ∧ E 0 = 1

private noncomputable def stieltjesTransform
    (μ : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ a in Set.Ioi (0 : ℝ),
    (1 : ℂ) / (z + (a : ℂ) ^ 2) ∂μ

private def stieltjesMeasureCarrier (μ : Measure ℝ) : Prop :=
  μ (Set.Iic (0 : ℝ)) = 0 ∧
    μ ({0} : Set ℝ) = 0

private def stieltjesLogDerivative
    (E : ℂ → ℂ) (μ : Measure ℝ) : Prop :=
  stieltjesMeasureCarrier μ ∧
    AnalyticOn ℂ (stieltjesTransform μ) slitPlane ∧
    (∀ w : ℝ, 0 < w →
      E (w : ℂ) ≠ 0 ∧
      deriv E (w : ℂ) / E (w : ℂ) =
        stieltjesTransform μ (w : ℂ))

/-- The positive-axis Stieltjes logarithmic derivative analytically continues
through the entire carrier to the slit-plane ODE; its zero orders therefore
exclude slit-plane zeros, and the squared lift has only imaginary zeros. -/
def claim15358 : Prop :=
  ∀ (E Y : ℂ → ℂ) (μ : Measure ℝ),
    entireSquaredCarrier E Y →
      stieltjesLogDerivative E μ →
      (∀ z : ℂ, z ∈ slitPlane →
        deriv E z = stieltjesTransform μ z * E z) ∧
      (∀ z : ℂ, E z = 0 → z ∈ nonpositiveRealAxis) ∧
      (∀ z : ℂ, Y z = 0 → z.re = 0)

end

end MathlibPlus.Open.ResearchFormalization.O0321Claim15358
