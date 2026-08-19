import MathlibPlus.Open.Combinatorics.FiniteGraphDeckClaims
import MathlibPlus.Open.ResearchFormalization.O0354LatticeTreePartition

open scoped Classical BigOperators
noncomputable section

namespace MathlibPlus.Open.Combinatorics.C0287KocayClaims

abbrev FiniteGraph := MathlibPlus.Open.Combinatorics.NR2.FiniteGraph

noncomputable def finiteGraphEdgeCount (F : FiniteGraph) : ℕ :=
  (MathlibPlus.Open.Combinatorics.NR2.graphEdgeFinset F.2).card

def edgeBlockMatches {n : ℕ} (A : Finset (Sym2 (Fin n)))
    (F : FiniteGraph) : Prop :=
  Nonempty ((MathlibPlus.Open.Combinatorics.NR2.blockFiniteGraph A).2 ≃g F.2)

noncomputable def spanningSubsetCount {n : ℕ} (F : FiniteGraph)
    (Y : SimpleGraph (Fin n)) : ℕ :=
  Fintype.card {A : Finset (Sym2 (Fin n)) //
    A ⊆ MathlibPlus.Open.Combinatorics.NR2.graphEdgeFinset Y ∧
      edgeBlockMatches A F}

noncomputable def orderedCoverCount {n k : ℕ} (F : Fin k → FiniteGraph)
    (Y : SimpleGraph (Fin n)) : ℕ :=
  Fintype.card {A : Fin k → Finset (Sym2 (Fin n)) //
    (∀ i, A i ⊆ MathlibPlus.Open.Combinatorics.NR2.graphEdgeFinset Y ∧
      edgeBlockMatches (A i) (F i)) ∧
      Finset.univ.biUnion A =
        MathlibPlus.Open.Combinatorics.NR2.graphEdgeFinset Y}

noncomputable def orderedPartitionCount {n k : ℕ}
    (F : Fin k → FiniteGraph) (Y : SimpleGraph (Fin n)) : ℕ :=
  Fintype.card {A : Fin k → Finset (Sym2 (Fin n)) //
    (∀ i, A i ⊆ MathlibPlus.Open.Combinatorics.NR2.graphEdgeFinset Y ∧
      edgeBlockMatches (A i) (F i)) ∧
      Finset.univ.biUnion A =
        MathlibPlus.Open.Combinatorics.NR2.graphEdgeFinset Y ∧
      ∀ e, e ∈ MathlibPlus.Open.Combinatorics.NR2.graphEdgeFinset Y →
        ∃! i, e ∈ A i}

def kTwo : FiniteGraph :=
  ⟨2, SimpleGraph.fromEdgeSet ({s(0, 1)} : Set (Sym2 (Fin 2)))⟩

def pathThree : FiniteGraph :=
  ⟨3, SimpleGraph.fromEdgeSet
    ({s(0, 1), s(1, 2)} : Set (Sym2 (Fin 3)))⟩

def twoDisjointEdges : FiniteGraph :=
  ⟨4, SimpleGraph.fromEdgeSet
    ({s(0, 1), s(2, 3)} : Set (Sym2 (Fin 4)))⟩

noncomputable def orderedHostEdgePairs {n : ℕ} (Y : SimpleGraph (Fin n)) :
    Finset (Sym2 (Fin n) × Sym2 (Fin n)) :=
  (MathlibPlus.Open.Combinatorics.NR2.graphEdgeFinset Y).product
    (MathlibPlus.Open.Combinatorics.NR2.graphEdgeFinset Y)

noncomputable def equalHostEdgePairs {n : ℕ} (Y : SimpleGraph (Fin n)) :
    Finset (Sym2 (Fin n) × Sym2 (Fin n)) :=
  (orderedHostEdgePairs Y).filter (fun p => p.1 = p.2)

noncomputable def adjacentHostEdgePairs {n : ℕ} (Y : SimpleGraph (Fin n)) :
    Finset (Sym2 (Fin n) × Sym2 (Fin n)) :=
  (orderedHostEdgePairs Y).filter (fun p =>
    p.1 ≠ p.2 ∧ ¬Disjoint p.1.toFinset p.2.toFinset)

noncomputable def disjointHostEdgePairs {n : ℕ} (Y : SimpleGraph (Fin n)) :
    Finset (Sym2 (Fin n) × Sym2 (Fin n)) :=
  (orderedHostEdgePairs Y).filter (fun p =>
    p.1 ≠ p.2 ∧ Disjoint p.1.toFinset p.2.toFinset)

/-- The exact `K₂,K₂` ordered-edge decomposition into equal, adjacent, and
 disjoint distinct pairs; the two latter classes are counted by `P₃` and
 `2K₂` edge-subset counts. -/
def claim4024_twoEdgeKocayIdentity : Prop :=
  ∀ {n : ℕ} (X : SimpleGraph (Fin n)),
    let m := (MathlibPlus.Open.Combinatorics.NR2.graphEdgeFinset X).card
    m ^ 2 = (equalHostEdgePairs X).card +
        (adjacentHostEdgePairs X).card + (disjointHostEdgePairs X).card ∧
      (equalHostEdgePairs X).card = m ∧
      (adjacentHostEdgePairs X).card = 2 * spanningSubsetCount pathThree X ∧
      (disjointHostEdgePairs X).card =
        2 * spanningSubsetCount twoDisjointEdges X

/-- `c(F,Y)` counts ordered edge-subset covers and `p(F;Y)` counts the same
 covers with every target edge occurring in exactly one part. -/
def claim4025_edgeCountTriangularity : Prop :=
  ∀ {n k : ℕ} (F : Fin k → FiniteGraph) (Y : SimpleGraph (Fin n)),
    let m := ∑ i : Fin k, finiteGraphEdgeCount (F i)
    ((MathlibPlus.Open.Combinatorics.NR2.graphEdgeFinset Y).card > m →
        orderedCoverCount F Y = 0) ∧
      ((MathlibPlus.Open.Combinatorics.NR2.graphEdgeFinset Y).card = m →
        orderedCoverCount F Y = orderedPartitionCount F Y)

abbrev UnlabeledGraph (n : ℕ) :=
  MathlibPlus.Combinatorics.Claim44521.finiteSimpleGraphType n

noncomputable def unlabeledRepresentative {n : ℕ} (Y : UnlabeledGraph n) :
    SimpleGraph (Fin n) :=
  Quotient.out Y

def noIsolatedType {n : ℕ} (Y : UnlabeledGraph n) : Prop :=
  ∀ v : Fin n, ∃ w : Fin n, (unlabeledRepresentative Y).Adj v w

abbrev SpanningGraphType (n : ℕ) :=
  {Y : UnlabeledGraph n // noIsolatedType Y}

abbrev ProperGraphPart (n : ℕ) :=
  Σ k : Fin n, {Y : UnlabeledGraph k // noIsolatedType Y}

noncomputable def properGraphRepresentative {n : ℕ} (F : ProperGraphPart n) :
    FiniteGraph :=
  ⟨F.1.1, unlabeledRepresentative F.2.1⟩

noncomputable def spanningGraphRepresentative {n : ℕ}
    (Y : SpanningGraphType n) : FiniteGraph :=
  ⟨n, unlabeledRepresentative Y.1⟩

abbrev KocayFamily (n k : ℕ) := Fin k → ProperGraphPart n
abbrev KocayRow (n : ℕ) := Σ k : ℕ, KocayFamily n k

noncomputable def kocayFamilyEdgeCount {n k : ℕ}
    (F : KocayFamily n k) : ℕ :=
  ∑ i : Fin k, finiteGraphEdgeCount (properGraphRepresentative (F i))

noncomputable def kocayRowEdgeCount {n : ℕ} (F : KocayRow n) : ℕ :=
  kocayFamilyEdgeCount F.2

noncomputable def kocayCoverCount {n k : ℕ} (F : KocayFamily n k)
    (Y : SpanningGraphType n) : ℕ :=
  orderedCoverCount (fun i => properGraphRepresentative (F i))
    (unlabeledRepresentative Y.1)

noncomputable def kocayPartitionCount {n k : ℕ}
    (F : KocayFamily n k) (Y : SpanningGraphType n) : ℕ :=
  orderedPartitionCount (fun i => properGraphRepresentative (F i))
    (unlabeledRepresentative Y.1)

noncomputable def kocayMatrix (n : ℕ) :
    Matrix (KocayRow n) (SpanningGraphType n) ℚ :=
  fun F Y => (kocayCoverCount F.2 Y : ℚ)

noncomputable def kocayLinearMap (n : ℕ) :
    (SpanningGraphType n →₀ ℚ) →ₗ[ℚ] (KocayRow n → ℚ) :=
  Finsupp.linearCombination ℚ
    (fun Y => fun F => kocayMatrix n F Y)

noncomputable def partitionLevelGraphType (n m : ℕ) :=
  {Y : SpanningGraphType n //
    finiteGraphEdgeCount (spanningGraphRepresentative Y) = m}

noncomputable def partitionLevelFamily (n m : ℕ) :=
  {F : KocayRow n // kocayRowEdgeCount F = m}

noncomputable def partitionColumn (n m : ℕ)
    (Y : partitionLevelGraphType n m) :
    partitionLevelFamily n m → ℚ :=
  fun F =>
    (kocayPartitionCount F.1.2 Y.1 : ℚ)

def reconstructionAtOrder (n : ℕ) : Prop :=
  ∀ G H : SimpleGraph (Fin n),
    MathlibPlus.Open.Combinatorics.FiniteGraphDeck.vertexDeck
        ⟨n, G⟩ =
      MathlibPlus.Open.Combinatorics.FiniteGraphDeck.vertexDeck
        ⟨n, H⟩ →
    Nonempty (G ≃g H)

/-- Independence of every edge-level ordered-partition block, with all finite
 part counts present as rows, is the stated sufficient criterion for the full
 Kocay kernel conclusion and reconstruction at that order. -/
def claim4026_orderedEdgePartitionSufficientCriterion : Prop :=
  ∀ n : ℕ,
    (∀ m : ℕ,
      LinearIndependent ℚ
        (fun Y : partitionLevelGraphType n m =>
          partitionColumn n m Y)) →
      LinearMap.ker (kocayLinearMap n) = ⊥ ∧
        reconstructionAtOrder n

noncomputable def treePartitionSignatures :
    Finset ((Set MathlibPlus.Open.Combinatorics.NR2.FiniteGraph) →₀ ℕ) :=
  (Finset.univ :
    Finset MathlibPlus.Open.ResearchFormalization.O0354.TreeType12).biUnion
    (fun T =>
      (MathlibPlus.Open.ResearchFormalization.O0354.treePartitionPolynomial T).support)

noncomputable def treePartitionMatrix :
    Matrix treePartitionSignatures
      MathlibPlus.Open.ResearchFormalization.O0354.TreeType12 ℚ :=
  fun σ T =>
    ((MvPolynomial.coeff σ.1
      (MathlibPlus.Open.ResearchFormalization.O0354.treePartitionPolynomial T) : ℤ) : ℚ)

noncomputable def treePartitionSupport
    (w : MathlibPlus.Open.ResearchFormalization.O0354.TreeType12 → ℤ) :
    Finset MathlibPlus.Open.ResearchFormalization.O0354.TreeType12 :=
  (Finset.univ :
    Finset MathlibPlus.Open.ResearchFormalization.O0354.TreeType12).filter
    (fun T => w T ≠ 0)

/-- The exact integer rank-deficient order-12 tree partition block.  The
integer witness is retained over the complete monomial coefficient system;
no conclusion about the full Kocay matrix or reconstruction is asserted. -/
def claim4027_uniformPartitionIndependenceFalse : Prop :=
  Fintype.card MathlibPlus.Open.ResearchFormalization.O0354.TreeType12 = 551 ∧
    Matrix.rank treePartitionMatrix = 550 ∧
    ∃ w : MathlibPlus.Open.ResearchFormalization.O0354.TreeType12 → ℤ,
      w ≠ 0 ∧
        (treePartitionSupport w).card = 105 ∧
        MathlibPlus.Open.ResearchFormalization.O0354.foldedPartitionPolynomial w = 0 ∧
        Matrix.mulVec treePartitionMatrix (fun T => (w T : ℚ)) = 0

end MathlibPlus.Open.Combinatorics.C0287KocayClaims
