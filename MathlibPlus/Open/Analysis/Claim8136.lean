import Mathlib

namespace MathlibPlus.Open.Analysis.Claim8136

/-- Claim 8136: the logarithm of the last-hole action is the displayed
collective logarithmic charge, with the source's positive domain and
`i < k` indexing made explicit. -/
def lastHoleLogChargeClaim8136 : Prop :=
  ∀ (M ck y xk : ℝ) (n k : ℕ) (x : ℕ → ℝ),
    0 < M →
    ck ≠ 0 →
    0 < y →
    0 < xk →
    (∀ i ∈ Finset.range k, xk < x i) →
    Real.log
        ((M / |ck|) * (y / xk) ^ n *
          ∏ i ∈ Finset.range k, ((x i + y) / (x i - xk)) ^ 2) =
      Real.log (M / |ck|) + n * Real.log (y / xk) +
        2 * ∑ i ∈ Finset.range k,
          Real.log ((x i + y) / (x i - xk))

end MathlibPlus.Open.Analysis.Claim8136
