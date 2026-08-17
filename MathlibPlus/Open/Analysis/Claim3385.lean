import MathlibPlus.Open.Analysis.Claim3384

namespace MathlibPlus.Open.Analysis.Claim3385

open MathlibPlus.Open.Analysis.Claim3381

/-- The consecutive-determinant ratio on the positive-determinant domain. -/
def determinantRatioFromLogCurvature : Prop :=
  ∀ (m n : ℕ),
    1 ≤ m →
    0 < D (m + 1) n →
    0 < D (m - 1) n →
    0 < D m (n - 1) →
    0 < D m n →
    0 < D m (n + 1) →
      D (m + 1) n * D (m - 1) n / D m n ^ 2 =
        1 - Real.exp (-(L m n))

end MathlibPlus.Open.Analysis.Claim3385
