import MathlibPlus.Open.ResearchFormalization.R0324HomogeneousDeckKernels

namespace MathlibPlus.Open.ResearchFormalization.R0324IsolateFreePrimitive

open MathlibPlus.Open.ResearchFormalization.R0324HomogeneousDeckKernels
open MathlibPlus.Open.ResearchFormalizationBatch

noncomputable section

/-- A graph type has an isolated vertex when its selected representative has one
vertex adjacent to no vertex. -/
def graphTypeHasIsolatedVertex {n : ℕ} (G : DeckGraphClass n) : Prop :=
  ∃ v : Fin n, ∀ w : Fin n, ¬ (Quotient.out G).Adj v w

/-- The exact isolate-free support condition for a graph-type vector. -/
def isolateFreeSupport {n : ℕ} (p : GraphSpace n) : Prop :=
  ∀ G : DeckGraphClass n, p G ≠ 0 → ¬ graphTypeHasIsolatedVertex G

/-- The edge-deletion kernel at a fixed graph order. -/
def edgeDeletionKernel (n : ℕ) : Set (GraphSpace n) :=
  {p | edgeDeletionOperator n p = 0}

/-- The vertex-deletion kernel at a fixed graph order. -/
def vertexDeletionKernel (n : ℕ) : Set (GraphSpace n) :=
  {p | vertexDeletionOperator n p = 0}

/-- The isolate-free primitive deck-flat vectors `P°_(n,r)`. -/
def isolateFreePrimitiveVectors (n r : ℕ) : Set (GraphSpace n) :=
  {p | edgeHomogeneous n r p ∧
    edgeDeletionOperator n p = 0 ∧
      isolateFreeSupport p}

/-- Claim 19862: the intersection of the vertex-deletion and edge-deletion
kernels with the fixed edge-rank space is exactly the isolate-free primitive
space. -/
def claim19862 : Prop :=
  ∀ (n r : ℕ),
    vertexDeletionKernel n ∩ edgeDeletionKernel n ∩
        {p | edgeHomogeneous n r p} =
      isolateFreePrimitiveVectors n r

end

end MathlibPlus.Open.ResearchFormalization.R0324IsolateFreePrimitive
