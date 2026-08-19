import MathlibPlus.Open.ResearchFormalization.O0352

namespace MathlibPlus.Open.ResearchFormalization.C0291Claim4080

open MathlibPlus.Open.ResearchFormalization.O0352
open MathlibPlus.Open.GraphTheory.PrivateSignatureFailureCensus

/-- Claim 4080: in the theorem range, the rational leaf-deck block has the
number of rows needed to attain the tree-level column-rank ceiling. -/
def claim4080_exactLeafDeckRank : Prop :=
  ∀ (n : ℕ), 3 ≤ n →
    letI : Fintype (TreeColumn n) := Fintype.ofFinite _
    Matrix.rank (leafDeckMatrix15580 n) = treeCount15580 (n - 1)

end MathlibPlus.Open.ResearchFormalization.C0291Claim4080
