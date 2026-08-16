import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Exact minimization and squared-reserve identity for the orientation-symmetrized Arthur-ray margin. -/
def claim11393_minimizationOverCompactPhase : Prop :=
  ∀ (θ U : ℝ),
    let x : ℝ := Real.cos θ ^ 2
    let H : ℝ := Real.exp U + Real.exp (-U)
    let K : ℝ := Real.exp U - Real.exp (-U)
    let margin : ℝ → ℝ := fun Φ =>
      (4 + 2 * x) * H +
        12 * Real.sqrt 2 * Real.sin θ * Real.cos θ * K * Real.sin Φ -
        8 * Real.cos Φ
    IsLeast (Set.range margin)
        ((4 + 2 * x) * H -
          Real.sqrt (288 * x * (1 - x) * K ^ 2 + 64)) ∧
      H ^ 2 - K ^ 2 = 4 ∧
      ((4 + 2 * x) * H) ^ 2 -
          (288 * x * (1 - x) * K ^ 2 + 64) =
        4 * (73 * x ^ 2 - 68 * x + 4) * K ^ 2 + 16 * x * (x + 4)

/-- Exact sharp phase window, including the margin, interval, and polynomial formulations. -/
def claim11394_sharpPhasePositivityWindow : Prop :=
  ∀ θ : ℝ,
    let x : ℝ := Real.cos θ ^ 2
    let xMinus : ℝ := (34 - 12 * Real.sqrt 6) / 73
    let xPlus : ℝ := (34 + 12 * Real.sqrt 6) / 73
    let polynomial : ℝ := 73 * x ^ 2 - 68 * x + 4
    let interval : Set ℝ := Set.Icc 0 xMinus ∪ Set.Icc xPlus 1
    let nonnegative : Prop :=
      ∀ (U Φ : ℝ),
        0 ≤
          (4 + 2 * x) * (Real.exp U + Real.exp (-U)) +
              12 * Real.sqrt 2 * Real.sin θ * Real.cos θ *
                (Real.exp U - Real.exp (-U)) * Real.sin Φ -
            8 * Real.cos Φ
    (nonnegative ↔ x ∈ interval) ∧
      (x ∈ interval ↔ 0 ≤ polynomial)

/-- Finite witness construction for every bad orientation phase. -/
def claim11395_finiteWitnessForBadPhase : Prop :=
  ∀ θ : ℝ,
    let x : ℝ := Real.cos θ ^ 2
    let polynomial : ℝ := 73 * x ^ 2 - 68 * x + 4
    polynomial < 0 →
      ∃ (K U Φ : ℝ),
        K ^ 2 = 1 - 4 * x * (x + 4) / polynomial ∧
          1 < K ^ 2 ∧
          K = 2 * Real.sinh U ∧
          K = Real.exp U - Real.exp (-U) ∧
          let H : ℝ := Real.exp U + Real.exp (-U)
          let margin : ℝ → ℝ := fun Ψ =>
            (4 + 2 * x) * H +
                12 * Real.sqrt 2 * Real.sin θ * Real.cos θ * K * Real.sin Ψ -
              8 * Real.cos Ψ
          IsLeast (Set.range margin) (margin Φ) ∧
            margin Φ = (4 + 2 * x) * H -
              Real.sqrt (288 * x * (1 - x) * K ^ 2 + 64) ∧
            ((4 + 2 * x) * H) ^ 2 -
                (288 * x * (1 - x) * K ^ 2 + 64) =
              4 * polynomial ∧
            4 * polynomial < 0 ∧
            margin Φ < 0

end MathlibPlus.Open.Analysis
