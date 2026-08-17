import MathlibPlus.Open.Research.K0013Exact

open scoped BigOperators

namespace MathlibPlus.Open.Research.K0013

/-- Claim 10516: the anti-diagonal coefficient formula, its symmetric
extension, and the unique bivariate formal-series Bezout quotient. -/
def claim10516 : Prop :=
  ∀ (α : ℝ) (j : ℕ),
    (∀ (u v : ℕ), u ≤ v →
      (PowerSeries.coeff u) ((PowerSeries.coeff v) (qSeries α j)) =
        ∑ k ∈ Finset.range (u + 1),
          (aCoeff α j k * pCoeff α j (u + v - k) -
            if 0 < k then
              pCoeff α j (k - 1) * aCoeff α j (u + v + 1 - k)
            else 0)) ∧
    (∀ (u v : ℕ), v < u →
      (PowerSeries.coeff u) ((PowerSeries.coeff v) (qSeries α j)) =
        ∑ k ∈ Finset.range (v + 1),
          (aCoeff α j k * pCoeff α j (u + v - k) -
            if 0 < k then
              pCoeff α j (k - 1) * aCoeff α j (u + v + 1 - k)
            else 0)) ∧
    (kernelW - kernelZ) * qSeries α j = kernelNumerator α j ∧
    (∀ Q : KernelSeries,
      (kernelW - kernelZ) * Q = kernelNumerator α j →
        Q = qSeries α j)

end MathlibPlus.Open.Research.K0013
