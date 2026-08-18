import MathlibPlus.Open.ResearchFormalization.R0337

namespace MathlibPlus.Open.ResearchFormalization.R0337

open scoped BigOperators
open ProjectsResearch.TreeDeck

/-- Claim 20059: the leaf-deck basis value is the sum over exactly the
degree-one vertex deletions, in the rational span of unlabelled trees. -/
def claim20059_actualLeafDeck : Prop :=
  ∀ (n : ℕ) (T : UnlabelledTree n),
    actualLeafDeck n (Finsupp.single T (1 : ℚ)) =
      ∑ ℓ : leafVertices T, Finsupp.single (leafCard T ℓ) (1 : ℚ)

end MathlibPlus.Open.ResearchFormalization.R0337
