import MathlibPlus.Open.Combinatorics.TreeOperators

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics.Claim10163

open MathlibPlus.Open.Combinatorics

attribute [local instance] Classical.propDecidable

private noncomputable def leafCount {n : ℕ} (q : GraphClass n) : ℕ :=
  (Finset.univ.filter (fun v : Fin n => isLeaf (graphRep q) v)).card

private noncomputable def leafDiagonalBasis {n : ℕ} (q : GraphClass n) : GraphSpace n :=
  (leafCount q : ℚ) • Finsupp.single q 1

private noncomputable def leafDiagonal (n : ℕ) : GraphSpace n →ₗ[ℚ] GraphSpace n :=
  extendBasis leafDiagonalBasis

/-- Claim 10163: the degree-weighted grafting commutator on the tree span. -/
def degreeWeightedGraftingCommutator : Prop :=
  ∀ (n : ℕ) (x : GraphSpace (n + 1)),
    x ∈ treeSpace (n + 1) →
      L (n + 1) (Gdeg (n + 1) x) - Gdeg n (L n x) =
        (2 * (((n + 1 : ℕ) : ℚ)) - 2) • x + leafDiagonal (n + 1) x

end MathlibPlus.Open.Combinatorics.Claim10163
