import MathlibPlus.Open.Combinatorics.R2667.Claim42272

namespace MathlibPlus.Open.Combinatorics.R2667.Claim42267

open MathlibPlus.Open.Combinatorics.UnionClosedBatch
open MathlibPlus.Open.Combinatorics.R2667.Claim42272

/-- Claim 42267: the coupled core is a proper union-closed subfamily, and
minimality supplies a residual deficit witness with the exact disjoint-delta
identity and the one/three tight-versus-outside lower bounds. -/
def claim42267 : Prop :=
  ∀ (G : Family14) (p₀ p₁ p₂ : Ground14)
    (R₁ R₂ : Finset Ground14),
    exactEndpoint14 G p₀ p₁ p₂ R₁ R₂ →
      let C := coupledCore14 G R₁ R₂
      let B := residualBlock14 G R₁ R₂
      unionClosed C ∧
        C.card < 53 ∧
        G = C ∪ B ∧
        Disjoint C B ∧
        ∃ y : Ground14,
          2 * frequency C y ≥ C.card ∧
            delta14 B y = delta14 G y - delta14 C y ∧
            delta14 B y ≥ delta14 G y ∧
            ((y ∈ tight14 p₀ p₁ p₂ → 1 ≤ delta14 B y) ∧
              (y ∉ tight14 p₀ p₁ p₂ → 3 ≤ delta14 B y))

end MathlibPlus.Open.Combinatorics.R2667.Claim42267
