import Mathlib

namespace MathlibPlus.Open.Analysis.PhaseBoundary

noncomputable section

/-- The leading Mellin multiplier on the stated gamma--Dini phase boundary. -/
def leadingPhaseBoundaryMultiplier (κ Y : ℝ) : ℝ :=
  1 - 4 * κ * (5 / 2 - Y) ^ 2 / Real.pi ^ 4

/-- The worst absolute multiplier residual on a height interval. -/
def phaseBoundaryResidual (Y₀ κ : ℝ) : ℝ :=
  sSup ((fun Y : ℝ => |leadingPhaseBoundaryMultiplier κ Y|) '' Set.Icc Y₀ (1 / 2))

/-- The scalar minimax value on a height interval. -/
def phaseBoundaryMinimax (Y₀ : ℝ) : ℝ :=
  sInf (Set.range (phaseBoundaryResidual Y₀))

/-- The sharp scalar minimax value for every allowed lower height. -/
def generalSharpScalarMinimax : Prop :=
  ∀ Y₀ : ℝ, 0 ≤ Y₀ → Y₀ ≤ 1 / 2 →
    phaseBoundaryMinimax Y₀ =
      ((5 / 2 - Y₀) ^ 2 - 4) / ((5 / 2 - Y₀) ^ 2 + 4)

/-- The unique whole-height minimizer and its endpoint residuals. -/
def wholeIntervalMinimax : Prop :=
  let kappaStar : ℝ := 2 * Real.pi ^ 4 / 41
  phaseBoundaryResidual 0 kappaStar = 9 / 41 ∧
    (∀ κ : ℝ, 9 / 41 ≤ phaseBoundaryResidual 0 κ) ∧
    (∀ κ : ℝ, phaseBoundaryResidual 0 κ = 9 / 41 → κ = kappaStar) ∧
    leadingPhaseBoundaryMultiplier kappaStar 0 = -(9 / 41) ∧
    leadingPhaseBoundaryMultiplier kappaStar (1 / 2) = 9 / 41

/-- No single scalar coefficient has an asymptotically vanishing whole-height residual. -/
def noOneScalarUniformCancellation : Prop :=
  ∀ κ : ℝ, 9 / 41 ≤ phaseBoundaryResidual 0 κ

end

end MathlibPlus.Open.Analysis.PhaseBoundary
