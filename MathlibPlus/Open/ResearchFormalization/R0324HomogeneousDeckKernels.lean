import MathlibPlus.Open.Research.FormalizationBatchDecks

namespace MathlibPlus.Open.ResearchFormalization.R0324HomogeneousDeckKernels

open scoped BigOperators
open Classical
open MathlibPlus.Open.ResearchFormalizationBatch

noncomputable section

/-- The rational vector space on isomorphism classes of `n`-vertex graphs. -/
abbrev GraphSpace (n : ℕ) := DeckGraphClass n →₀ ℚ

/-- Edge rank of the chosen representative of an isomorphism class. -/
def edgeRank {n : ℕ} (G : DeckGraphClass n) : ℕ :=
  (Quotient.out G).edgeSet.ncard

/-- The homogeneous edge-rank predicate for the graph-type span. -/
def edgeHomogeneous (n k : ℕ) (x : GraphSpace n) : Prop :=
  ∀ G : DeckGraphClass n, edgeRank G ≠ k → x G = 0

/-- A basis vector for a graph isomorphism class. -/
def graphBasis {n : ℕ} (G : DeckGraphClass n) : GraphSpace n :=
  Finsupp.single G 1

/-- The vertex-deletion operator is defined on graph types by the exact deck
operation from the selected representative. -/
def vertexDeletionBasis (n : ℕ) (G : DeckGraphClass n) :
    GraphSpace (n - 1) :=
  ∑ v : Fin n,
    graphBasis (vertexCard (Quotient.out G) v)

def vertexDeletionOperator (n : ℕ) :
    GraphSpace n →ₗ[ℚ] GraphSpace (n - 1) :=
  Finsupp.linearCombination ℚ (vertexDeletionBasis n)

/-- Delete one edge while retaining the graph's vertex carrier. -/
def edgeDeletionGraph {n : ℕ} (G : DeckGraph n) (e : Sym2 (Fin n)) :
    DeckGraph n :=
  SimpleGraph.fromRel (fun v w => G.Adj v w ∧ Sym2.mk v w ≠ e)

/-- Add one nonedge while retaining the graph's vertex carrier. -/
def edgeAdditionGraph {n : ℕ} (G : DeckGraph n) (e : Sym2 (Fin n)) :
    DeckGraph n :=
  SimpleGraph.fromRel (fun v w => G.Adj v w ∨ Sym2.mk v w = e)

/-- All nonedges of a finite graph. -/
def deckNonedgeFinset {n : ℕ} (G : DeckGraph n) :
    Finset (Sym2 (Fin n)) :=
  (Finset.univ : Finset (Sym2 (Fin n))).filter
    (fun e => e ∉ G.edgeSet ∧ e ∈ (⊤ : SimpleGraph (Fin n)).edgeSet)

/-- Edge deletion and edge addition on the graph-type span. -/
def edgeDeletionBasis (n : ℕ) (G : DeckGraphClass n) : GraphSpace n :=
  ∑ e ∈ deckEdgeFinset (Quotient.out G),
    graphBasis (deckClass (edgeDeletionGraph (Quotient.out G) e))

def edgeAdditionBasis (n : ℕ) (G : DeckGraphClass n) : GraphSpace n :=
  ∑ e ∈ deckNonedgeFinset (Quotient.out G),
    graphBasis (deckClass (edgeAdditionGraph (Quotient.out G) e))

def edgeDeletionOperator (n : ℕ) :
    GraphSpace n →ₗ[ℚ] GraphSpace n :=
  Finsupp.linearCombination ℚ (edgeDeletionBasis n)

def edgeAdditionOperator (n : ℕ) :
    GraphSpace n →ₗ[ℚ] GraphSpace n :=
  Finsupp.linearCombination ℚ (edgeAdditionBasis n)

/-- The homogeneous deck kernel `K_(n,k) = ker(D | V_(n,k))`, with the
homogeneous carrier and the deck-flat equation both explicit. -/
def homogeneousDeckKernel (n k : ℕ) : Set (GraphSpace n) :=
  {x | edgeHomogeneous n k x ∧ vertexDeletionOperator n x = 0}

/-- A finite word of edge operations, with `true` meaning edge addition and
`false` meaning edge deletion. -/
def edgeWord (n : ℕ) : List Bool → GraphSpace n → GraphSpace n
  | [], x => x
  | true :: w, x => edgeWord n w (edgeAdditionOperator n x)
  | false :: w, x => edgeWord n w (edgeDeletionOperator n x)

/-- Edge rank after interpreting a word of additions and deletions. -/
def edgeRankAfter : ℕ → List Bool → ℕ
  | k, [] => k
  | k, true :: w => edgeRankAfter (k + 1) w
  | k, false :: w => edgeRankAfter (k - 1) w

/-- Claim 19858: the exact graph-type homogeneous deck kernels are stable under
edge lowering and raising, and hence remain deck-flat along every typed edge
operation word. -/
def claim19858 : Prop :=
  ∀ (n k : ℕ) (x : GraphSpace n),
    x ∈ homogeneousDeckKernel n k →
      edgeDeletionOperator n x ∈ homogeneousDeckKernel n (k - 1) ∧
        edgeAdditionOperator n x ∈ homogeneousDeckKernel n (k + 1) ∧
        ∀ (w : List Bool),
          edgeWord n w x ∈
            homogeneousDeckKernel n (edgeRankAfter k w)

end
end MathlibPlus.Open.ResearchFormalization.R0324HomogeneousDeckKernels
