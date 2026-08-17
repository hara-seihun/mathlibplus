import MathlibPlus.Open.Analysis.DepthNormIdentityK0125

namespace MathlibPlus.Open.Analysis.LambertFullNormActionK0125

noncomputable section

open MathlibPlus.Open.Analysis.DepthNormIdentityK0125

/-- The model's squared monic norm, retaining the `μ₀` normalization from the
orthogonal-polynomial carrier. -/
def starNorm (μ₀ : ℝ) (k : ℕ) : ℝ :=
  μ₀ * compactNorm k

/-- The model coefficient `c_N^* = a_N^*`. -/
def starCoefficient (N : ℕ) : ℝ :=
  compactCoefficient N

/-- The terminally rescaled full norm ratio. -/
def fullNormRatio (μ₀ : ℝ) (n : ℕ) : ℝ :=
  starNorm μ₀ n /
    (μ₀ * (starCoefficient (2 * n)) ^ (4 * n))

/-- The normalized logarithmic full action. -/
def normalizedFullNormAction (μ₀ : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * Real.log (fullNormRatio μ₀ n)

/-- Claim 8894: the exact terminal action, its `O(W_(2n)/n)` remainder,
and its limit. -/
def claim_8894 : Prop :=
  ∀ μ₀ : ℝ, 0 < μ₀ →
    (∀ n : ℕ, 0 < n →
      Real.log (fullNormRatio μ₀ n) =
        2 * trailingLambertAction 0 (2 * n)) ∧
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ =>
        normalizedFullNormAction μ₀ n -
          4 * (1 - (compactLambertWNat (2 * n))⁻¹))
      (fun n : ℕ => compactLambertWNat (2 * n) / (n : ℝ)) ∧
    Filter.Tendsto
      (fun n : ℕ => normalizedFullNormAction μ₀ n)
      Filter.atTop (nhds 4)

end

end MathlibPlus.Open.Analysis.LambertFullNormActionK0125
