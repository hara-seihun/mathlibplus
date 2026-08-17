import MathlibPlus.Open.Analysis.DepthNormIdentityK0125

namespace MathlibPlus.Open.Analysis.CompactLambertCoefficientModelK0125

noncomputable section

open MathlibPlus.Open.Analysis.DepthNormIdentityK0125

/-- Claim 8888: the one-based compact Lambert coefficient and its exponential
representation.  The definitions opened above supply
`W(x) = W₀(x/(2π))` and `W_j = W(j)`. -/
def claim_8888 : Prop :=
  ∀ j : ℕ, 0 < j →
    compactCoefficient j =
        compactLambertWNat j / (4 * (j : ℝ)) ∧
      compactLambertWNat j / (4 * (j : ℝ)) =
        Real.exp (-(compactLambertWNat j)) / (8 * Real.pi)

end

end MathlibPlus.Open.Analysis.CompactLambertCoefficientModelK0125
