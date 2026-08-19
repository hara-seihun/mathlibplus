import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.C0047Claim747

/-- The normalized FKS tail has the displayed logarithmic derivative and is
strictly decreasing above the exact threshold.  The decreasing conclusion is
written pointwise to keep the threshold and order of the arguments explicit. -/
def normalizedTailMonotonicity_claim747 : Prop :=
  let R : ℝ := 5.5666305
  let h : ℝ → ℝ := fun L =>
    121.0961 * (L / R) ^ (3 / 2 : ℝ) *
        Real.exp (-2 * Real.sqrt (L / R)) * L ^ (3 : ℕ)
  (∀ L : ℝ, 0 < L →
      deriv h L / h L = 9 / (2 * L) - 1 / Real.sqrt (R * L)) ∧
    81 * R / 4 = 112.724267625 ∧
    (∀ L₁ L₂ : ℝ, 81 * R / 4 < L₁ → L₁ < L₂ → h L₂ < h L₁)

end MathlibPlus.Open.ResearchFormalization.C0047Claim747
