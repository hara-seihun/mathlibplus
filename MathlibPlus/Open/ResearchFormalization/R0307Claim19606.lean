import MathlibPlus.Open.Graphs.BasisTranspose
import MathlibPlus.Open.ResearchFormalization.R0307GraphDeckClaim19602

open scoped BigOperators

open MathlibPlus.Open.Graphs

namespace MathlibPlus.Open.ResearchFormalization.R0307Claim19606

noncomputable section

abbrev GraphSpace19606 (n : ℕ) := GraphIsoClass n →₀ ℚ

noncomputable def graphInsertion19606 (n : ℕ) :
    GraphSpace19606 n →ₗ[ℚ] GraphSpace19606 (n + 1) :=
  R0307GraphDeckClaim19602.allAttachmentInsertion n

noncomputable def graphDeck19606 (n : ℕ) :
    GraphSpace19606 (n + 1) →ₗ[ℚ] GraphSpace19606 n :=
  R0307GraphDeckClaim19602.fullVertexDeck n

noncomputable def graphCount19606 (n : ℕ) : ℕ :=
  Fintype.card (GraphIsoClass n)

noncomputable def graphWeightedPairing19606 {n : ℕ}
    (x y : GraphSpace19606 n) : ℚ :=
  ∑ G ∈ x.support,
    x G * y G * graphAutWeight n G

def graphOrthogonal19606 {n : ℕ}
    (A B : Submodule ℚ (GraphSpace19606 n)) : Prop :=
  ∀ x : GraphSpace19606 n, x ∈ A →
    ∀ y : GraphSpace19606 n, y ∈ B →
      graphWeightedPairing19606 x y = 0

def graphOrthogonalDecomposition19606 {n : ℕ}
    (A B : Submodule ℚ (GraphSpace19606 n)) : Prop :=
  A ⊔ B = ⊤ ∧ A ⊓ B = ⊥ ∧ graphOrthogonal19606 A B

noncomputable def graphKernelDimension19606 (n : ℕ) : ℕ :=
  Module.finrank ℚ (LinearMap.ker (graphDeck19606 n))

/-- Claim 19606: the full graph level splits as the orthogonal sum of the
range of all-attachment insertion and the kernel of the full vertex deck;
the kernel dimension is the difference of the graph-class counts, including
its six displayed values at orders one through six. -/
def claim19606 : Prop :=
  (∀ n : ℕ,
    graphOrthogonalDecomposition19606
      (LinearMap.range (graphInsertion19606 n))
      (LinearMap.ker (graphDeck19606 n)) ∧
    graphKernelDimension19606 n =
      graphCount19606 (n + 1) - graphCount19606 n) ∧
  graphKernelDimension19606 0 = 0 ∧
  graphKernelDimension19606 1 = 1 ∧
  graphKernelDimension19606 2 = 2 ∧
  graphKernelDimension19606 3 = 7 ∧
  graphKernelDimension19606 4 = 23 ∧
  graphKernelDimension19606 5 = 122

end

end MathlibPlus.Open.ResearchFormalization.R0307Claim19606
