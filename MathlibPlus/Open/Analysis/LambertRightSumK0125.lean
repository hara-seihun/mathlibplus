import MathlibPlus.Open.Analysis.DepthNormIdentityK0125

open scoped Interval

namespace MathlibPlus.Open.Analysis.LambertRightSumK0125

noncomputable section

open MathlibPlus.Open.Analysis.DepthNormIdentityK0125

/-- The continuous comparison carrier from `m` to `N`, with the Lambert
height `W_N-W(x)` inside the integral. -/
def trailingLambertIntegral (m N : ℕ) : ℝ :=
  ∫ x in (m : ℝ)..(N : ℝ),
    compactLambertWNat N - compactLambertW x

/-- Claim 8891: the sharp monotone bracket and its explicit right-sum
asymptotic. -/
def claim_8891 : Prop :=
  (∀ (m N : ℕ), 0 ≤ m → m < N →
    0 ≤ trailingLambertIntegral m N - trailingLambertAction m N ∧
      trailingLambertIntegral m N - trailingLambertAction m N ≤
        compactLambertWNat N - compactLambertWNat m) ∧
    compactLambertWNat 0 = 0 ∧
    Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ =>
        trailingLambertAction 0 N -
          (N : ℝ) * (1 - (compactLambertWNat N)⁻¹))
      (fun N : ℕ => compactLambertWNat N)

end

end MathlibPlus.Open.Analysis.LambertRightSumK0125
