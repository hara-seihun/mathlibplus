import MathlibPlus.Open.Research.R0338QuadraticDeck

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.Research.R0338Claim20082

open MathlibPlus.Open.Research.R0338

/-- Claim 20082: the exact quadratic chromatic-deck feature space is the full
function space on the realized unlabeled trees for orders four through ten,
with its dimension equal to the tree-index cardinality. -/
def claim20082_quadraticObservationsRealizeEveryFunction : Prop :=
  ∀ n : ℕ, 4 ≤ n → n ≤ 10 →
    quadraticFeatureSpace n = ⊤ ∧
      Module.finrank ℚ (quadraticFeatureSpace n) =
        (realizedTrees n).card

end MathlibPlus.Open.Research.R0338Claim20082
