import Mathlib

namespace MathlibPlus.Open.Analysis.CHJII

noncomputable section

open Set
open MeasureTheory

/-- The weight data and the normalization used by the CHJ-II claims. -/
def admissibleCHJIIWeight (ξ : ℝ) (w : ℝ → ℝ) : Prop :=
  1 < ξ ∧
    ContDiffOn ℝ 1 w (Icc 1 ξ) ∧
    (∀ u ∈ Icc 1 ξ, 0 ≤ w u) ∧
    (∫ u in (1 : ℝ)..ξ, w u) = 1

/-- The norm appearing in the CHJ-II source-intersection formula. -/
def chjNorm (ξ : ℝ) (w : ℝ → ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ *
    (w ξ / ξ + w 1 +
      (∫ u in (1 : ℝ)..ξ, w u / u) +
      (∫ u in (1 : ℝ)..ξ, |deriv w u| / u))

/-- The first moment appearing in the CHJ-II source-intersection formula. -/
def chjLength (ξ : ℝ) (w : ℝ → ℝ) : ℝ :=
  Real.pi⁻¹ * (∫ u in (1 : ℝ)..ξ, u * w u)

/-- The source-intersection equation forces the square-root norm floor. -/
def sourceEquationSquareRootNormFloor : Prop :=
  ∀ (ξ : ℝ) (w : ℝ → ℝ) (θ : ℝ),
    admissibleCHJIIWeight ξ w →
      0 < θ →
        2 * chjNorm ξ w / θ ^ 2 = 1 + θ * chjLength ξ w →
          4 * chjNorm ξ w / θ =
              2 * θ * (1 + θ * chjLength ξ w) ∧
            2 * Real.sqrt (2 * chjNorm ξ w) < 4 * chjNorm ξ w / θ

/-- The dual-test coefficient and its test function for the small-ratio regime. -/
def smallRatioCoefficient (ξ : ℝ) : ℝ :=
  (1 + ξ⁻¹ + Real.log ξ) / (ξ - 1)

def smallRatioTestFunction (ξ u : ℝ) : ℝ :=
  1 + Real.log u - smallRatioCoefficient ξ * (u - 1)

/-- The explicit small-ratio dual test and its lower bound for the CHJ-II norm. -/
def smallRatioDualTest : Prop :=
  ∀ (ξ : ℝ),
    1 < ξ →
      ξ ≤ 2 →
        smallRatioCoefficient ξ > 2 ∧
          smallRatioTestFunction ξ 1 = 1 ∧
            smallRatioTestFunction ξ ξ = -ξ⁻¹ ∧
              (∀ u ∈ Icc 1 ξ,
                |smallRatioTestFunction ξ u| ≤ u⁻¹) ∧
                (∀ w : ℝ → ℝ,
                  admissibleCHJIIWeight ξ w →
                    2 * Real.pi * chjNorm ξ w ≥ smallRatioCoefficient ξ)

end

end MathlibPlus.Open.Analysis.CHJII
