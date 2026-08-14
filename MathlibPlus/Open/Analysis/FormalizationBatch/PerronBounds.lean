import Mathlib

namespace MathlibPlus.Open.Analysis.FormalizationBatch

/-- The common-contour source condition appearing in claim 12398. -/
def commonContourSourceCondition (u : ℝ) : Prop :=
  let α : ℝ := (817 : ℝ) / 50000
  let L : ℝ := 3575
  α * L > u + Real.log 2 + Real.log (1 + Real.exp (-u))

/-- Claim 12396: the normalized exponent-63 Perron term is strictly decreasing
and exceeds 1.518 at u = 56. -/
def normalizedExponent63PerronTerm : Prop :=
  let z₀ : ℝ := 1946
  let α : ℝ := (817 : ℝ) / 50000
  let ω : ℝ := (397 : ℝ) / 500
  let K : ℝ := (1421 : ℝ) / 1000
  let F : ℝ := 4 / ((1 - α) * Real.rpow z₀ (1 - ω))
  let P₀ : ℝ := 2 * K + 2 * F * Real.sqrt (2 / Real.pi)
  let L : ℝ := 3575
  let m : ℝ := 63
  let h : ℝ := m * Real.exp (-L / m)
  let E_trunc : ℝ → ℝ := fun u =>
    P₀ / m * Real.exp (L / m - u) *
      ((1 + h) * Real.rpow (L + Real.log (1 + h)) (1 - ω) +
        Real.rpow L (1 - ω))
  StrictAnti E_trunc ∧ E_trunc 56 > (1518 : ℝ) / 1000

/-- Claim 12398: the right side of the source-height condition is strictly
increasing, reverses the condition at u = 58 by more than 0.2776, and hence
excludes all u ≥ 58. -/
def sourceHeightCeiling : Prop :=
  let α : ℝ := (817 : ℝ) / 50000
  let L : ℝ := 3575
  let rhs : ℝ → ℝ := fun u =>
    u + Real.log 2 + Real.log (1 + Real.exp (-u))
  StrictMono rhs ∧
    rhs 58 - α * L > (2776 : ℝ) / 10000 ∧
    ∀ u : ℝ, 58 ≤ u → ¬ commonContourSourceCondition u

end MathlibPlus.Open.Analysis.FormalizationBatch
