import Mathlib
import MathlibPlus.Combinatorics.Claim44521

open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics.NR2Kocay

noncomputable section

abbrev GraphType (n : ℕ) :=
  MathlibPlus.Combinatorics.Claim44521.finiteSimpleGraphType n

noncomputable def graphRepresentative {n : ℕ} (Y : GraphType n) : SimpleGraph (Fin n) :=
  Quotient.out Y

noncomputable def graphEdges {n : ℕ} (Y : GraphType n) : Finset (Sym2 (Fin n)) :=
  letI := Classical.decEq (Sym2 (Fin n))
  letI := Classical.propDecidable
  Finset.univ.filter (fun e => e ∈ (graphRepresentative Y).edgeSet)

def graphEdgeCount {n : ℕ} (Y : GraphType n) : ℕ :=
  (graphEdges Y).card

noncomputable def graphSpanCount {n : ℕ} (Y : GraphType n) : ℕ :=
  letI := Classical.decEq (Fin n)
  letI := Classical.propDecidable
  (Finset.univ.filter (fun v => ∃ w, (graphRepresentative Y).Adj v w)).card

def graphHasNoIsolatedVertices {n : ℕ} (Y : GraphType n) : Prop :=
  ∀ v : Fin n, ∃ w : Fin n, (graphRepresentative Y).Adj v w

def graphIsTree {n : ℕ} (Y : GraphType n) : Prop :=
  (graphRepresentative Y).IsTree

abbrev EdgeLevelColumn (n m : ℕ) :=
  {Y : GraphType n // graphEdgeCount Y = m ∧ graphHasNoIsolatedVertices Y}

noncomputable def blockVertices {n : ℕ}
    (B : Finset (Sym2 (Fin n))) : Finset (Fin n) :=
  letI := Classical.decEq (Fin n)
  B.biUnion (fun e => e.toFinset)

def blockSpansFewerThan {n : ℕ}
    (B : Finset (Sym2 (Fin n))) : Prop :=
  (blockVertices B).card < n

noncomputable def blockGraphType {n : ℕ}
    (B : Finset (Sym2 (Fin n))) : GraphType n :=
  MathlibPlus.Combinatorics.Claim44521.graphTypeOf n
    (SimpleGraph.fromEdgeSet (B : Set (Sym2 (Fin n))))

def EdgeLevelFamily (n m k : ℕ) :=
  {F : Fin k → GraphType n //
    (∀ i, 0 < graphEdgeCount (F i) ∧ graphSpanCount (F i) < n) ∧
      ∑ i, graphEdgeCount (F i) = m}

noncomputable def orderedEdgePartitionCount {n m k : ℕ}
    (F : EdgeLevelFamily n m k) (Y : EdgeLevelColumn n m) : ℕ :=
  letI := Classical.decEq (Sym2 (Fin n))
  letI := Classical.propDecidable
  Fintype.card {π : Fin k → Finset (Sym2 (Fin n)) //
    (∀ i, (π i).Nonempty ∧ π i ⊆ graphEdges Y.1 ∧
      blockSpansFewerThan (π i) ∧ blockGraphType (π i) = F.1 i) ∧
      (∀ e, e ∈ graphEdges Y.1 ↔ ∃ i, e ∈ π i) ∧
      (∀ i j, i ≠ j → Disjoint (π i) (π j))}

def AllEdgeLevelRow (n m : ℕ) :=
  {r : Σ k : Fin (m + 1), (Fin k.val → GraphType n) //
    (∀ i, 0 < graphEdgeCount (r.2 i) ∧ graphSpanCount (r.2 i) < n) ∧
      ∑ i, graphEdgeCount (r.2 i) = m}

noncomputable def allPartFamily (r : AllEdgeLevelRow n m) :
    EdgeLevelFamily n m r.1.1.val :=
  ⟨r.1.2, r.2⟩

noncomputable def allPartPartitionMatrix (n m : ℕ) :
    Matrix (AllEdgeLevelRow n m) (EdgeLevelColumn n m) ℚ :=
  fun r Y => orderedEdgePartitionCount (allPartFamily r) Y

noncomputable def levelColumnCard (n m : ℕ) : ℕ :=
  letI := Classical.propDecidable
  letI := Fintype.ofFinite (EdgeLevelColumn n m)
  Fintype.card (EdgeLevelColumn n m)

noncomputable def allPartPartitionRank (n m : ℕ) : ℕ :=
  letI := Classical.propDecidable
  letI : Finite (AllEdgeLevelRow n m) :=
    Finite.of_injective (f := fun r : AllEdgeLevelRow n m => r.1)
      Subtype.val_injective
  letI := Fintype.ofFinite (AllEdgeLevelRow n m)
  letI := Fintype.ofFinite (EdgeLevelColumn n m)
  Matrix.rank (allPartPartitionMatrix n m)

noncomputable def fixedPartPartitionMatrix (n m k : ℕ) :
    Matrix (EdgeLevelFamily n m k) (EdgeLevelColumn n m) ℚ :=
  fun F Y => orderedEdgePartitionCount F Y

noncomputable def fixedPartPartitionRank (n m k : ℕ) : ℕ :=
  letI := Classical.propDecidable
  letI : Finite (EdgeLevelFamily n m k) :=
    Finite.of_injective (f := fun F : EdgeLevelFamily n m k => F.1)
      Subtype.val_injective
  letI := Fintype.ofFinite (EdgeLevelFamily n m k)
  letI := Fintype.ofFinite (EdgeLevelColumn n m)
  Matrix.rank (fixedPartPartitionMatrix n m k)

/-- Three distinct columns can be pairwise separated without being linearly independent. -/
def claim4028_columnInjectivityInsufficientForTriangularProof : Prop :=
  ∃ (v₁ v₂ v₃ : Fin 2 → ℚ),
    v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ ∧
      v₁ + v₂ = (2 : ℚ) • v₃ ∧
      ¬ LinearIndependent ℚ (fun i : Fin 3 => ![v₁, v₂, v₃] i)

/-- The order-five all-part-count partition blocks have the listed sizes and full ranks. -/
def claim4029_orderFivePartitionBlocksFullRank : Prop :=
  (∀ i : Fin 8,
    levelColumnCard 5 (i.val + 3) =
      (![1, 4, 5, 5, 4, 2, 1, 1] i) ∧
    allPartPartitionRank 5 (i.val + 3) =
      levelColumnCard 5 (i.val + 3))

/-- The additional exact order-six and order-seven partition-block ranks. -/
def claim4030_additionalExactPartitionBlockRanks : Prop :=
  (∀ i : Fin 7,
    levelColumnCard 6 (i.val + 3) =
      (![1, 3, 9, 15, 20, 22, 20] i) ∧
    allPartPartitionRank 6 (i.val + 3) =
      levelColumnCard 6 (i.val + 3)) ∧
    levelColumnCard 7 6 = 20 ∧
    allPartPartitionRank 7 6 = 20 ∧
    ∀ Y : GraphType 7, graphIsTree Y →
      ∃ Z : EdgeLevelColumn 7 6, Z.1 = Y

/-- At order five and edge count four, two-part rows have rank four but three-part rows have rank two. -/
def claim4031_quantificationOverAllPartCountsEssential : Prop :=
  levelColumnCard 5 4 = 4 ∧
    fixedPartPartitionRank 5 4 2 = 4 ∧
    fixedPartPartitionRank 5 4 3 = 2 ∧
    fixedPartPartitionRank 5 4 3 ≠ levelColumnCard 5 4

end

end MathlibPlus.Open.Combinatorics.NR2Kocay
