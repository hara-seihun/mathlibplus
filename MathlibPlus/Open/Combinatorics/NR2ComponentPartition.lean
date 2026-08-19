import Mathlib
import MathlibPlus.Open.Combinatorics.NR2OrderedEdgePartition
import MathlibPlus.Open.GraphTheory.PrivateSignatureFailureCensus

open scoped BigOperators

open MathlibPlus.Open.Combinatorics.NR2

namespace MathlibPlus.Open.Combinatorics.NR2ComponentPartition

noncomputable section

abbrev GraphType (n : ℕ) :=
  MathlibPlus.Open.GraphTheory.PrivateSignatureFailureCensus.GraphType n

abbrev LevelGraphType (n m : ℕ) :=
  MathlibPlus.Open.GraphTheory.PrivateSignatureFailureCensus.LevelGraphType n m

noncomputable def representativeGraph {n : ℕ} (Y : GraphType n) :
    SimpleGraph (Fin n) :=
  MathlibPlus.Open.GraphTheory.PrivateSignatureFailureCensus.graphRepresentative Y

def graphEdgeCount {n : ℕ} (Y : GraphType n) : ℕ :=
  MathlibPlus.Open.GraphTheory.PrivateSignatureFailureCensus.graphEdgeCount Y

def hasNoIsolatedVertices {n : ℕ} (Y : GraphType n) : Prop :=
  MathlibPlus.Open.GraphTheory.PrivateSignatureFailureCensus.hasNoIsolatedVertices Y

abbrev GraphMotif :=
  Sigma (fun k : ℕ => {G : SimpleGraph (Fin k) // ∀ v, ∃ w, G.Adj v w})

def motifType (F : GraphMotif) : Set FiniteGraph :=
  {H | Nonempty (F.2.1 ≃g H.2)}

def motifEdgeCount (F : GraphMotif) : ℕ :=
  (graphEdgeFinset F.2.1).card

def familyEdgeCount {k : ℕ} (F : Fin k → GraphMotif) : ℕ :=
  ∑ i : Fin k, motifEdgeCount (F i)

def familySignature {k : ℕ} (F : Fin k → GraphMotif) :
    Set FiniteGraph →₀ ℕ :=
  ∑ i : Fin k, Finsupp.single (motifType (F i)) 1

def familyMonomial {k : ℕ} (F : Fin k → GraphMotif) :
    MvPolynomial (Set FiniteGraph) ℕ :=
  ∏ i : Fin k, MvPolynomial.X (motifType (F i))

def familyNormalization {k : ℕ} (F : Fin k → GraphMotif) : ℚ :=
  ((Nat.card {σ : Equiv.Perm (Fin k) //
      ∀ i, motifType (F i) = motifType (F (σ i))} : ℕ) : ℚ)⁻¹

def OrderedFamily (n : ℕ) :=
  Σ k : ℕ, {F : Fin k → GraphMotif // ∀ i, (F i).1 < n}

abbrev LevelFamily (n m : ℕ) :=
  {F : OrderedFamily n // familyEdgeCount F.2.1 = m}

def coveringTuple {n k : ℕ} (F : Fin k → GraphMotif)
    (G : SimpleGraph (Fin n)) :=
  {B : Fin k → Finset (Sym2 (Fin n)) //
    (∀ i, (B i).Nonempty ∧
      B i ⊆ graphEdgeFinset G ∧
      blockSpansFewerThan (B i) ∧
      Nonempty ((F i).2.1 ≃g (blockFiniteGraph (B i)).2)) ∧
    Finset.univ.biUnion B = graphEdgeFinset G}

def coveringCount {n k : ℕ} (F : Fin k → GraphMotif)
    (G : SimpleGraph (Fin n)) : ℕ :=
  Nat.card (coveringTuple F G)

def coveringSystemEntry {n m : ℕ} (F : LevelFamily n m)
    (Y : LevelGraphType n m) : ℚ :=
  coveringCount F.1.2.1 (representativeGraph Y.1)

def validPartitionPolynomial {n : ℕ} (G : SimpleGraph (Fin n)) :
    MvPolynomial (Set FiniteGraph) ℤ :=
  orderedEdgePartitionPolynomial G

def levelPartitionPolynomial {n m : ℕ} (Y : LevelGraphType n m) :
    MvPolynomial (Set FiniteGraph) ℤ :=
  validPartitionPolynomial (representativeGraph Y.1)

def componentEdgeSpan {n : ℕ} (B : Finset (Sym2 (Fin n))) :
    Finset (Fin n) :=
  B.biUnion (fun e => e.toFinset)

noncomputable def componentEdgeBlock {n : ℕ} (G : SimpleGraph (Fin n))
    (C : G.ConnectedComponent) : Finset (Sym2 (Fin n)) :=
  letI : DecidablePred
      (fun e : Sym2 (Fin n) =>
        (e.toFinset : Set (Fin n)) ⊆ (C : Set (Fin n))) :=
    Classical.decPred _
  (graphEdgeFinset G).filter
    (fun e => (e.toFinset : Set (Fin n)) ⊆ (C : Set (Fin n)))

noncomputable def componentEdgePartition {n : ℕ}
    (G : SimpleGraph (Fin n)) : Finset (Finset (Sym2 (Fin n))) :=
  letI : DecidableEq G.ConnectedComponent := Classical.decEq _
  (Finset.univ : Finset G.ConnectedComponent).image
    (componentEdgeBlock G)

def componentSignature {n : ℕ} (G : SimpleGraph (Fin n)) :
    Set FiniteGraph →₀ ℕ :=
  Finset.sum (componentEdgePartition G)
    (fun B => Finsupp.single (blockGraphType B) 1)

def componentMonomial {n : ℕ} (G : SimpleGraph (Fin n)) :
    MvPolynomial (Set FiniteGraph) ℤ :=
  ∏ B ∈ componentEdgePartition G,
    MvPolynomial.X (blockGraphType B)

def componentSpanCard {n : ℕ} (G : SimpleGraph (Fin n))
    (C : G.ConnectedComponent) : ℕ :=
  (componentEdgeSpan (componentEdgeBlock G C)).card

def componentVertexCount {n : ℕ} (G : SimpleGraph (Fin n))
    (C : G.ConnectedComponent) : ℕ :=
  Nat.card {v : Fin n // v ∈ (C : Set (Fin n))}

def edgePartition {n : ℕ} (G : SimpleGraph (Fin n))
    (blocks : Finset (Finset (Sym2 (Fin n)))) : Prop :=
  (∀ B ∈ blocks, B.Nonempty ∧ B ⊆ graphEdgeFinset G) ∧
    blocks.biUnion id = graphEdgeFinset G ∧
    (∀ B ∈ blocks, ∀ C ∈ blocks, B ≠ C → Disjoint B C)

def spanUnion {n : ℕ} (blocks : Finset (Finset (Sym2 (Fin n)))) :
    Finset (Fin n) :=
  blocks.biUnion componentEdgeSpan

def claim4057_validEdgePartitionAndPartitionPolynomial : Prop :=
  ∀ (n m : ℕ), 3 ≤ n →
    ∃ scalar : LevelFamily n m → ℚ,
      (∀ F, scalar F ≠ 0) ∧
      (∀ Y : LevelGraphType n m,
        levelPartitionPolynomial Y =
          validPartitionPolynomial (representativeGraph Y.1) ∧
        ∀ F : LevelFamily n m,
          MvPolynomial.coeff
              (familySignature F.1.2.1)
              (levelPartitionPolynomial Y) =
            scalar F * coveringSystemEntry F Y)

def claim4058_componentPartitionIsValid : Prop :=
  ∀ (n m : ℕ) (Y : LevelGraphType n m), 3 ≤ n →
    let G := representativeGraph Y.1
    (¬ G.Connected ∧ 2 ≤ Fintype.card G.ConnectedComponent) →
      (∀ C : G.ConnectedComponent, componentSpanCard G C ≤ n - 1) ∧
      admissibleEdgePartition G (componentEdgePartition G) ∧
      componentSignature G ∈ (validPartitionPolynomial G).support

def claim4059_spanCountingCollapse : Prop :=
  ∀ (n m : ℕ) (Y Z : LevelGraphType n m), 3 ≤ n →
    let G := representativeGraph Y.1
    let H := representativeGraph Z.1
    (¬ G.Connected ∧ 2 ≤ Fintype.card G.ConnectedComponent) →
      ∀ blocks : Finset (Finset (Sym2 (Fin n))),
        edgePartition H blocks →
        ∀ assignment : G.ConnectedComponent ≃
            {B : Finset (Sym2 (Fin n)) // B ∈ blocks},
          (∀ C : G.ConnectedComponent,
            Nonempty (G.induce (C : Set (Fin n)) ≃g
              (blockFiniteGraph (assignment C).1).2)) →
            spanUnion blocks = Finset.univ ∧
            (spanUnion blocks).card = n ∧
            (spanUnion blocks).card ≤
              ∑ B ∈ blocks, (componentEdgeSpan B).card ∧
            (spanUnion blocks).card ≤
              ∑ C : G.ConnectedComponent, componentVertexCount G C ∧
            (∑ B ∈ blocks, (componentEdgeSpan B).card =
              ∑ C : G.ConnectedComponent, componentVertexCount G C) ∧
            (∑ C : G.ConnectedComponent, componentVertexCount G C = n) ∧
            (blocks : Set (Finset (Sym2 (Fin n)))).PairwiseDisjoint
              componentEdgeSpan ∧
            Nonempty (H ≃g G)

def claim4060_privateComponentSplitMonomial : Prop :=
  ∀ (n m : ℕ) (Y : LevelGraphType n m), 3 ≤ n →
    let G := representativeGraph Y.1
    (¬ G.Connected ∧ 2 ≤ Fintype.card G.ConnectedComponent) →
      componentSignature G ∈ (validPartitionPolynomial G).support ∧
      ∀ Z : LevelGraphType n m, Z ≠ Y →
        componentSignature G ∉
          (validPartitionPolynomial (representativeGraph Z.1)).support

end

end MathlibPlus.Open.Combinatorics.NR2ComponentPartition
