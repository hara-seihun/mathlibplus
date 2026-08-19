import MathlibPlus.Basic

open scoped BigOperators

namespace MathlibPlus.Algebra.Claim1153

/-- The shift `b=a-1/2` used by the principal product. -/
noncomputable def shiftedPairParameter (a : ℝ) : ℝ :=
  a - 1 / 2

/-- The shifted principal pair-sum product
`P_d(b) = d! ∏_{0≤p<q≤d} (2b+p+q+1)`. -/
noncomputable def shiftedPrincipalPairSumProduct (d : ℕ) (b : ℝ) : ℝ :=
  (d.factorial : ℝ) *
    (∏ p ∈ Finset.range (d + 1),
      (∏ q ∈ Finset.Ioc p d,
        (2 * b + (p : ℝ) + (q : ℝ) + 1)))

/-- The accompanying shifted variable `X = 2b+d+1`. -/
def shiftedPrincipalX (d : ℕ) (b : ℝ) : ℝ :=
  2 * b + (d : ℝ) + 1

end MathlibPlus.Algebra.Claim1153
