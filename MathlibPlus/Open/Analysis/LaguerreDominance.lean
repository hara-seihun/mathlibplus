import Mathlib

namespace MathlibPlus.Open.Analysis

open scoped BigOperators

/-- The generalized Laguerre polynomial with parameter `2`, in the normalization
specified by the admitted expansion. -/
noncomputable def generalizedLaguerreTwo (d : ℕ) (t : ℝ) : ℝ :=
  Finset.sum (Finset.range (d + 1)) (fun k =>
    (-1 : ℝ) ^ k *
      (Nat.choose (d + 2) (d - k) : ℝ) *
      t ^ k / (Nat.factorial k : ℝ))

/-- The sum of the absolute ratios of the lower terms to the leading monomial. -/
noncomputable def generalizedLaguerreTwoLowerTermRatio (d : ℕ) (t : ℝ) : ℝ :=
  Finset.sum (Finset.range d) (fun k =>
    |((-1 : ℝ) ^ k *
        (Nat.choose (d + 2) (d - k) : ℝ) *
        t ^ k / (Nat.factorial k : ℝ)) /
      (t ^ d / (Nat.factorial d : ℝ))|)

def generalizedLaguerreTwoThreshold (d : ℕ) : ℝ :=
  4 * (d : ℝ) * ((d + 2 : ℕ) : ℝ)

/-- Leading monomial domination for generalized Laguerre polynomials beyond
`4*d*(d+2)`. -/
def leadingMonomialDominatesBeyond : Prop :=
  ∀ d : ℕ, ∀ t : ℝ,
    d ≥ 1 →
      generalizedLaguerreTwoThreshold d ≤ t →
      generalizedLaguerreTwoLowerTermRatio d t ≤ Real.exp (1 / 4) - 1 ∧
        ((-1 : ℝ) ^ d * generalizedLaguerreTwo d t ≥
            (2 - Real.exp (1 / 4)) * t ^ d / (Nat.factorial d : ℝ) ∧
          (2 - Real.exp (1 / 4)) * t ^ d / (Nat.factorial d : ℝ) > 0)

end MathlibPlus.Open.Analysis
