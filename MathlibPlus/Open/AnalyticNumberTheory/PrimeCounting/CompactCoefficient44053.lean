import Mathlib

/-!
# The coefficient-44.053 compact prime-counting packet

Statement-fidelity registry nodes for claims 840 and 842.  The real prime
counting function is represented by `Nat.primeCounting ⌊x⌋₊`, so integer
endpoints are included.
-/

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-- Claim 840: the exact polynomial-arithmetic lower bound on the compact gap.

The packet's `s_A` is unfolded at `A = 44.053`, and `U` is the degree-16
rational majorant displayed in claim 835. -/
def asymptoticCompactGapLowerBound_claim840 : Prop :=
  ∀ L : ℝ, 3000 ≤ L →
    let t : ℝ := 1 / L
    let s : ℝ := 1 - t - t ^ 2 - 3 * t ^ 3 - ((44053 : ℝ) / 1000) * t ^ 4
    let U : ℝ :=
      (∑ j in Finset.range 16, (Nat.factorial j : ℝ) / L ^ j) +
        ((1673823191040000 : ℝ) / 23) / L ^ 16
    ((155265 : ℝ) / 10000) / L ^ 4 < s⁻¹ - U

/-- Claim 842: the improved compact prime-counting inequality with coefficient
`44.053`, on the complete range `x ≥ 29.53`. -/
def improvedCompactPrimeCounting_claim842 : Prop :=
  ∀ x : ℝ, (2953 : ℝ) / 100 ≤ x →
    (Nat.primeCounting ⌊x⌋₊ : ℝ) <
      x / (Real.log x - 1 - (Real.log x)⁻¹ -
        3 / (Real.log x) ^ 2 - ((44053 : ℝ) / 1000) / (Real.log x) ^ 3)

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
