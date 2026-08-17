import MathlibPlus.Open.Analysis.ResearchFormalizeR0438

open Filter
open scoped BigOperators Topology

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R0521.Claim22290

open MathlibPlus.Open.Analysis

/-- The normalized dense-tail gap train. -/
def denseTailGap (q ε : ℝ) (i : ℤ) : ℝ :=
  (ε + q ^ Int.natAbs i) / (1 + ε)

/-- Roots obtained recursively from the dense-tail gaps, with x₀ = 0. -/
def denseTailRoot (q ε : ℝ) (i : ℤ) : ℝ :=
  if 0 ≤ i then
    ∑ k ∈ Finset.range (Int.toNat i), denseTailGap q ε (k : ℤ)
  else
    -∑ k ∈ Finset.range (Int.toNat (-i)),
      denseTailGap q ε (-((k : ℤ) + 1))

/-- Claim 22290: the central and neighboring pressures have the stated limits
for the explicit dense-tail family, together with its reflection symmetry. -/
def claim22290 : Prop :=
  ∀ q : ℝ, 0 < q → q < 1 →
    Tendsto
        (fun ε : ℝ => ε * pressure (denseTailRoot q ε) 0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (2 * Real.log q)) ∧
      Tendsto
        (fun ε : ℝ => ε * pressure (denseTailRoot q ε) 1)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (-q * Real.log ((1 + q - q ^ 2) / q))) ∧
      ∀ ε : ℝ, 0 < ε →
        gap (denseTailRoot q ε) (-1) = gap (denseTailRoot q ε) 1 ∧
          pressure (denseTailRoot q ε) (-1) =
            pressure (denseTailRoot q ε) 1

end MathlibPlus.Open.ResearchFormalization.R0521.Claim22290
