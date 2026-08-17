import MathlibPlus.Open.Combinatorics.R2667.Claim42272

namespace MathlibPlus.Open.Combinatorics.R2667.Claim42268

open MathlibPlus.Open.Combinatorics.R2667.Claim42272

/-- Claim 42268: every member of the exact residual block has the three
root returns into the two generated upper families and their intersection. -/
def claim42268_threeRootReturns : Prop :=
  ∀ (G : Family14) (p₀ p₁ p₂ : Ground14)
    (R₁ R₂ : Finset Ground14),
    exactEndpoint14 G p₀ p₁ p₂ R₁ R₂ →
      let J := R₁ ∪ R₂
      let B := residualBlock14 G R₁ R₂
      ∀ ⦃A : Finset Ground14⦄, A ∈ B →
        A ∪ R₁ ∈ rootUpperFamily14 G R₁ ∧
          A ∪ R₂ ∈ rootUpperFamily14 G R₂ ∧
          A ∪ J ∈ rootUpperFamily14 G R₁ ∧
          A ∪ J ∈ rootUpperFamily14 G R₂

end MathlibPlus.Open.Combinatorics.R2667.Claim42268
