import MathlibPlus.Open.Research.R3193.Claim47053

open scoped BigOperators

namespace MathlibPlus.Open.Research.R3193

noncomputable section

/-- In the shared-bit Rademacher model, the equal-weight component mean has
balanced unit-variance components, off-diagonal covariance `p^2`, and the
corresponding exact variance. -/
def claim47048 : Prop :=
  ∀ n : ℕ, 0 < n →
    (∀ j : Fin n,
      componentMean n j = 0 ∧ componentVariance n j = 1) ∧
    (∀ j k : Fin n, j ≠ k →
      componentCovariance n j k = p ^ 2) ∧
    V n = (1 + ((n : ℝ) - 1) * p ^ 2) / (n : ℝ)

end

end MathlibPlus.Open.Research.R3193
