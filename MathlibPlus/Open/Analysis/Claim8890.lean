import MathlibPlus.Open.Analysis.DepthNormIdentityK0125

open scoped Interval

namespace MathlibPlus.Open.Analysis.Claim8890

open MathlibPlus.Open.Analysis.DepthNormIdentityK0125

/-- The exact continuous integral for the trailing Lambert block, with the
endpoint split at `m = 0`. -/
def claim_8890_exactContinuousTrailingLambertIntegral : Prop :=
  ∀ (m N : ℕ),
    0 ≤ m →
    m < N →
    let W : ℝ → ℝ := compactLambertW
    let Wnat : ℕ → ℝ := compactLambertWNat
    let S : ℝ := ∑ j ∈ Finset.Ioc m N, (Wnat N - Wnat j)
    let I : ℝ := ∫ x in (m : ℝ)..(N : ℝ), W (N : ℝ) - W x
    (0 < m →
        I = (N : ℝ) * (1 - 1 / Wnat N) -
          (m : ℝ) * (Wnat N - Wnat m + 1 - 1 / Wnat m)) ∧
      (m = 0 →
        I = (N : ℝ) * (1 - 1 / Wnat N) + 2 * Real.pi)

end MathlibPlus.Open.Analysis.Claim8890
