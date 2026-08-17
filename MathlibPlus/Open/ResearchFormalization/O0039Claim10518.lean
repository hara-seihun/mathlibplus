import MathlibPlus.Open.ResearchFormalizationBatch_01a006da607a7b6d8b4cd04d89586ca5

namespace MathlibPlus.Open.ResearchFormalization.O0039Claim10518

open MathlibPlus.Open.ResearchFormalizationBatch_01a006da607a7b6d8b4cd04d89586ca5

noncomputable section

/-- The Darboux pivot ratio from the admitted peel. -/
def pivotRatio (α : ℝ) (j : ℕ) : ℝ :=
  ((α + (j : ℝ) + 1) *
      (2 * α - (2 * ((j + 1 : ℕ) : ℝ) - 1))) /
    (2 * (4 * (j : ℝ) + 1) *
      (4 * (j : ℝ) + 3) ^ 2 * (4 * (j : ℝ) + 5))

/-- The positive factor in the pivot-denominator recurrence. -/
def pivotDenomStep (j : ℕ) : ℝ :=
  2 * (4 * (j : ℝ) + 1) *
    (4 * (j : ℝ) + 3) ^ 2 * (4 * (j : ℝ) + 5)

/-- The pivot ratio and explicit gamma-pivot formula. -/
def claim10518 : Prop :=
  ∀ (α : ℝ) (j : ℕ),
    let d : ℕ → ℝ := gammaPivot α
    let q : ℕ → ℝ := pivotDenom
    d 0 = α / 2 ∧
      (d j ≠ 0 → d (j + 1) / d j = pivotRatio α j) ∧
      d j =
        ((Finset.prod (Finset.range (j + 1)) (fun u => α + (u : ℝ))) *
          (Finset.prod (Finset.range j) (fun u =>
            2 * α - (2 * ((u + 1 : ℕ) : ℝ) - 1)))) /
          q j ∧
      q 0 = 2 ∧
      q (j + 1) / q j = pivotDenomStep j ∧
      0 < pivotDenomStep j

end

end MathlibPlus.Open.ResearchFormalization.O0039Claim10518
