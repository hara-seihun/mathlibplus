import MathlibPlus.Open.Combinatorics.R2667.Claim42272

namespace MathlibPlus.Open.Combinatorics.R2667.Claim42275

open MathlibPlus.Open.Combinatorics.UnionClosedBatch

abbrev Ground14 := MathlibPlus.Open.Combinatorics.R2667.Claim42272.Ground14
abbrev Family14 := MathlibPlus.Open.Combinatorics.R2667.Claim42272.Family14

abbrev exactEndpoint14 :=
  MathlibPlus.Open.Combinatorics.R2667.Claim42272.exactEndpoint14

def tight14 (p₀ p₁ p₂ : Ground14) : Finset Ground14 :=
  {p₀, p₁, p₂}

/-- The finite endpoint constraints, with the two root laws displayed as
Horn implications on ordinary finite families. -/
def endpointConstraintSystem14 (G : Family14)
    (p₀ p₁ p₂ : Ground14) (R₁ R₂ : Finset Ground14) : Prop :=
  G.card = 53 ∧
    frequency G p₀ = 26 ∧
    frequency G p₁ = 26 ∧
    frequency G p₂ = 26 ∧
    (∀ x : Ground14,
      x ∉ tight14 p₀ p₁ p₂ → frequency G x ≤ 25) ∧
    R₁ ∉ G ∧
    R₂ ∉ G ∧
    R₁ ∪ R₂ ∈ G ∧
    (∀ ⦃A : Finset Ground14⦄,
      A ∈ G → ¬ A ⊆ R₁ → A ∪ R₁ ∈ G) ∧
    (∀ ⦃A : Finset Ground14⦄,
      A ∈ G → ¬ A ⊆ R₂ → A ∪ R₂ ∈ G) ∧
    unionClosed G

/-- The normalized endpoint is an exact finite ordinary-family constraint
system, not a trace or weighted relaxation. -/
def claim42275 : Prop :=
  ∀ (G : Family14) (p₀ p₁ p₂ : Ground14)
    (R₁ R₂ : Finset Ground14),
    exactEndpoint14 G p₀ p₁ p₂ R₁ R₂ →
      endpointConstraintSystem14 G p₀ p₁ p₂ R₁ R₂

end MathlibPlus.Open.Combinatorics.R2667.Claim42275
