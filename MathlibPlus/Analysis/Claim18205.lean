import Mathlib

namespace MathlibPlus.Analysis.Claim18205

/-- The positive real roots of the rank-indexed source polynomial `C_r`. -/
def positiveRootSet (C : ℕ → Polynomial ℝ) (r : ℕ) : Set ℝ :=
  {x | 0 < x ∧ (C r).eval x = 0}

/-- The wall threshold attached to rank `r`, represented by the supremum of its
positive-root set.  Existence of a largest root is kept as the separate
`IsGreatest` specification rather than silently assumed by this definition. -/
noncomputable def wallThreshold (C : ℕ → Polynomial ℝ) (r : ℕ) : ℝ :=
  sSup (positiveRootSet C r)

/-- The source phrase “`Q_r` is the largest positive real root of `C_r`”. -/
def wallThresholdIsLargestPositiveRoot (C : ℕ → Polynomial ℝ)
    (r : ℕ) (Q : ℝ) : Prop :=
  IsGreatest (positiveRootSet C r) Q

end MathlibPlus.Analysis.Claim18205
