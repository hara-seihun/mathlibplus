import Mathlib

namespace MathlibPlus.Open.Analysis

/--
For positive `t`, the sum of the absolute ratios of the lower terms in the
finite generalized Laguerre expansion to `t^d / d!` is bounded by the stated
reindexed factorial sum.
-/
def laguerreLowerTermRatioEstimate : Prop :=
  ∀ (d : ℕ) (t : ℝ),
    0 < t →
      (Finset.sum (Finset.range d) (fun k =>
          |(((-1 : ℝ) ^ k) * (Nat.choose (d + 2) (d - k) : ℝ) *
              t ^ k / (Nat.factorial k : ℝ)) /
            (t ^ d / (Nat.factorial d : ℝ))|)) ≤
        Finset.sum (Finset.Icc (1 : ℕ) d) (fun r =>
          (1 / (Nat.factorial r : ℝ)) *
            (((d : ℝ) * ((d : ℝ) + 2)) / t) ^ r)

end MathlibPlus.Open.Analysis
