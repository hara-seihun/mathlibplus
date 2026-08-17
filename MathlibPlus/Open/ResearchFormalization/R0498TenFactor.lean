import MathlibPlus.Open.Research.FormalizationBatch

namespace MathlibPlus.Open.ResearchFormalization.R0498

open scoped BigOperators
noncomputable section

open MathlibPlus.Open.Research.FormalizationBatch

/-- The positive-factor ceiling formula used at `ell = 10`. -/
def tenFactorCeilingU (ell N : ℕ) : ℕ :=
  1 +
      ∑ a ∈ Finset.Icc 1 (((ell + 1) / 2) - 1),
        (N + 1 - 2 * a) +
    if Even ell then ((N + 2) / 2 - ell / 2) else 0

/-- Claim 29365: exact ten-factor attainment in every cell and the stable
`N ≥ 10` dimension formula. -/
def exactTenFactorAttainment : Prop :=
  (∀ N : ℕ,
    fixedTotalFactorProductSpanDimension 10 N = tenFactorCeilingU 10 N) ∧
  (∀ N : ℕ, 10 ≤ N →
    fixedTotalFactorProductSpanDimension 10 N = 4 * N + N / 2 - 19)

end

end MathlibPlus.Open.ResearchFormalization.R0498
