import Mathlib

open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal

namespace MathlibPlus.Open.ResearchFormalization.O0321Claim15357

noncomputable section

private def slitPlane : Set ℂ :=
  {z : ℂ | ¬ (z.im = 0 ∧ z.re ≤ 0)}

private def entireSquaredCarrier (E Y : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ E Set.univ ∧
    AnalyticOnNhd ℂ Y Set.univ ∧
    (∀ z : ℂ, Y z = E (z ^ 2)) ∧
    Y 0 = 1 ∧ E 0 = 1

private def completelyMonotone (k : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ⊤ k (Set.Ioi (0 : ℝ)) ∧
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n k x

private noncomputable def levyMeasure (k : ℝ → ℝ) : Measure ℝ :=
  Measure.withDensity volume (fun x =>
    ENNReal.ofReal (k |x| / |x|))

private def symmetricMeasure (μ : Measure ℝ) : Prop :=
  ∀ A : Set ℝ, MeasurableSet A →
    μ A = μ {x : ℝ | -x ∈ A}

private def levyIntegrable (k : ℝ → ℝ) : Prop :=
  ∫⁻ x : ℝ, ENNReal.ofReal (min (1 : ℝ) (x ^ 2))
      ∂levyMeasure k < ∞

private def levyNumeratorCarrier (Y : ℂ → ℂ) (k : ℝ → ℝ) : Prop :=
  completelyMonotone k ∧
    symmetricMeasure (levyMeasure k) ∧
    levyIntegrable k ∧
    (∀ t : ℝ,
      Complex.log (Y (t : ℂ)) =
        ((2 * ∫ x in Set.Ioi (0 : ℝ),
          (1 - Real.cos (t * x)) * k x / x) : ℂ))

private noncomputable def stieltjesTransform
    (μ : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ a in Set.Ioi (0 : ℝ),
    (1 : ℂ) / (z + (a : ℂ) ^ 2) ∂μ

private def stieltjesMeasureCarrier (μ : Measure ℝ) : Prop :=
  μ (Set.Iic (0 : ℝ)) = 0 ∧
    μ ({0} : Set ℝ) = 0

/-- Complete monotonicity supplies a Bernstein measure on the positive
half-line, the exact Stieltjes quotient on the positive axis, and the
analytic Stieltjes transform on the slit plane. -/
def claim15357 : Prop :=
  ∀ (E Y : ℂ → ℂ) (k : ℝ → ℝ),
    entireSquaredCarrier E Y →
      levyNumeratorCarrier Y k →
      ∃ μ : Measure ℝ,
        stieltjesMeasureCarrier μ ∧
        (∀ x : ℝ, 0 < x →
          k x = ∫ a in Set.Ioi (0 : ℝ),
            Real.exp (-a * x) ∂μ) ∧
        (∀ w : ℝ, 0 < w →
          E (w : ℂ) ≠ 0 ∧
          deriv E (w : ℂ) / E (w : ℂ) =
            stieltjesTransform μ (w : ℂ)) ∧
        AnalyticOn ℂ (stieltjesTransform μ) slitPlane

end

end MathlibPlus.Open.ResearchFormalization.O0321Claim15357
