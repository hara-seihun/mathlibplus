import Mathlib

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace MathlibPlus.Open.NewResearch2.R0171Repair

noncomputable section

/-- The density carried by the logarithmic cell for the integer `n` and the
nested tail beginning at `M`. -/
def logCellDensity (M : ℕ) (y : ℝ) : ENNReal :=
  ∑' n : ℕ,
    (if M ≤ n ∧ Real.log (n : ℝ) ≤ y ∧
        y < Real.log ((n : ℝ) + 1) then
      ENNReal.ofReal (Real.exp y - n)
    else 0)

/-- The positive measure on the nested logarithmic tail. -/
def logCellTailMeasure (M : ℕ) : Measure ℝ :=
  (Measure.withDensity volume (logCellDensity M)).restrict
    (Ici (Real.log M))

/-- The raw reflection-folded tail in the integral representation. -/
def rawFoldedTail (M : ℕ) (z : ℂ) : ℂ :=
  2 * ∫ y : ℝ,
    (Real.exp (-y / 2) : ℂ) * Complex.cosh (z * (y : ℂ))
      ∂ logCellTailMeasure M

/-- The positive even moment appearing after passing to the coordinate
`w = -z²`. -/
def positiveEvenMoment (M j : ℕ) : ℝ :=
  (2 / (Nat.factorial (2 * j) : ℝ)) *
    ∫ y : ℝ, y ^ (2 * j) * Real.exp (-y / 2)
      ∂ logCellTailMeasure M

/-- The evaluation fold formed from the positive even moments. -/
def evenMomentEvaluation (M : ℕ) (z : ℝ) : ℝ :=
  ∑' j : ℕ, positiveEvenMoment M j * z ^ (2 * j)

/-- Claim 18524: the raw fold has the displayed even-moment coefficients in
`w = -z²`, and every such coefficient is strictly positive after the
checkerboard sign is removed. -/
def claim18524_foldedCoefficientsPositiveEvenMoments : Prop :=
  ∀ M : ℕ, 0 < M →
    ∃ a : ℕ → ℝ,
      (∀ z : ℂ, |z.re| < (1 / 2 : ℝ) →
        rawFoldedTail M z =
          ∑' j : ℕ, (a j : ℂ) * (-z ^ 2) ^ j) ∧
      ∀ j : ℕ,
        (-1 : ℝ) ^ j * a j = positiveEvenMoment M j ∧
          0 < positiveEvenMoment M j

/-- Claim 18529: for the actual two-cut even-moment evaluations, the first
cut is positive and the projective slope `E₂/E₁` is continuous and strictly
increasing on the stated half-open interval. -/
def claim18529_rawTwoCutProjectiveSlopeIncreasing : Prop :=
  let E : ℕ → ℝ → ℝ := evenMomentEvaluation
  let y : ℝ → ℝ := fun z => E 2 z / E 1 z
  (∀ z : ℝ, 0 ≤ z → z < (1 / 2 : ℝ) → 0 < E 1 z) ∧
    ContinuousOn y (Ico 0 (1 / 2 : ℝ)) ∧
    StrictMonoOn y (Ico 0 (1 / 2 : ℝ))

end

end MathlibPlus.Open.NewResearch2.R0171Repair
