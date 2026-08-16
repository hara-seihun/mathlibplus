import MathlibPlus.Open.GraphTheory.PrivateSignatureFailureCensus

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.O0352

open MathlibPlus.Open.GraphTheory.PrivateSignatureFailureCensus

/-- The finite tree columns used by the tree-level covering matrix. -/
abbrev TreeColumn (n : ℕ) :=
  {Y : LevelGraphType n (n - 1) // (graphRepresentative Y.1).IsTree}

noncomputable instance treeColumnFinite (n : ℕ) : Finite (TreeColumn n) := by
  apply Finite.of_injective (f := fun T : TreeColumn n => T.1.1)
  intro A B h
  apply Subtype.ext
  apply Subtype.ext
  exact h

noncomputable instance treeColumnFintype (n : ℕ) : Fintype (TreeColumn n) :=
  Fintype.ofFinite _

/-- The signature of a two-block edge partition, retaining the two block types
as a multiset (and hence retaining multiplicity when the types coincide). -/
noncomputable def partitionSignature {n : ℕ}
    (π : Finset (Finset (Sym2 (Fin n)))) : GraphType n →₀ ℕ :=
  ∑ B ∈ π, Finsupp.single (blockType B) 1

/-- The one-edge small-part condition for the leaf-deck rows. -/
def isLeafSmallBlock {n : ℕ} (B : Finset (Sym2 (Fin n))) : Prop :=
  B.card = 1

/-- The separated two-edge shape `2K₂`. -/
def isTwoMatchingBlock {n : ℕ} (B : Finset (Sym2 (Fin n))) : Prop :=
  B.card = 2 ∧
    ∀ v : Fin n,
      (SimpleGraph.fromEdgeSet (B : Set (Sym2 (Fin n)))).degree v ≤ 1

/-- The separated two-edge shape `P₃`. -/
def isPathThreeBlock {n : ℕ} (B : Finset (Sym2 (Fin n))) : Prop :=
  B.card = 2 ∧
    ∃ v : Fin n,
      (SimpleGraph.fromEdgeSet (B : Set (Sym2 (Fin n)))).degree v = 2

/-- The signatures represented by valid two-block partitions whose small side
has one edge. -/
noncomputable def leafRowSet15580 (n : ℕ) :
    Finset (GraphType n →₀ ℕ) := by
  classical
  exact (Finset.univ : Finset (TreeColumn n)).biUnion (fun T =>
    ((validEdgePartitions T.1.1).filter (fun π =>
      π.card = 2 ∧ ∃ B ∈ π, isLeafSmallBlock B)).image partitionSignature)

/-- The signatures represented by valid two-block partitions whose two-edge
small side is `2K₂`. -/
noncomputable def twoMatchingRowSet15580 (n : ℕ) :
    Finset (GraphType n →₀ ℕ) := by
  classical
  exact (Finset.univ : Finset (TreeColumn n)).biUnion (fun T =>
    ((validEdgePartitions T.1.1).filter (fun π =>
      π.card = 2 ∧ ∃ B ∈ π, isTwoMatchingBlock B)).image partitionSignature)

/-- The signatures represented by valid two-block partitions whose two-edge
small side is `P₃`. -/
noncomputable def pathThreeRowSet15580 (n : ℕ) :
    Finset (GraphType n →₀ ℕ) := by
  classical
  exact (Finset.univ : Finset (TreeColumn n)).biUnion (fun T =>
    ((validEdgePartitions T.1.1).filter (fun π =>
      π.card = 2 ∧ ∃ B ∈ π, isPathThreeBlock B)).image partitionSignature)

/-- The rows obtained by adjoining one separated two-edge family to the leaf
rows. -/
noncomputable def leafPlusMatchingRows15580 (n : ℕ) :
    Finset (GraphType n →₀ ℕ) :=
  leafRowSet15580 n ∪ twoMatchingRowSet15580 n

/-- The rows obtained by adjoining the `P₃` two-edge family to the leaf rows. -/
noncomputable def leafPlusPathThreeRows15580 (n : ℕ) :
    Finset (GraphType n →₀ ℕ) :=
  leafRowSet15580 n ∪ pathThreeRowSet15580 n

abbrev LeafRow15580 (n : ℕ) :=
  {μ : GraphType n →₀ ℕ // μ ∈ leafRowSet15580 n}

abbrev LeafPlusMatchingRow15580 (n : ℕ) :=
  {μ : GraphType n →₀ ℕ // μ ∈ leafPlusMatchingRows15580 n}

abbrev LeafPlusPathThreeRow15580 (n : ℕ) :=
  {μ : GraphType n →₀ ℕ // μ ∈ leafPlusPathThreeRows15580 n}

noncomputable def partitionEntry15580 {n : ℕ}
    (μ : GraphType n →₀ ℕ) (T : TreeColumn n) : ℚ :=
  (partitionPolynomial T.1).coeff μ

noncomputable def leafDeckMatrix15580 (n : ℕ) :
    Matrix (LeafRow15580 n) (TreeColumn n) ℚ :=
  fun μ T => partitionEntry15580 μ.1 T

noncomputable def leafPlusMatchingMatrix15580 (n : ℕ) :
    Matrix (LeafPlusMatchingRow15580 n) (TreeColumn n) ℚ :=
  fun μ T => partitionEntry15580 μ.1 T

noncomputable def leafPlusPathThreeMatrix15580 (n : ℕ) :
    Matrix (LeafPlusPathThreeRow15580 n) (TreeColumn n) ℚ :=
  fun μ T => partitionEntry15580 μ.1 T

noncomputable def treeCount15580 (n : ℕ) : ℕ :=
  Fintype.card (TreeColumn n)

/-- Claim 15580: the exact separated two-edge rank data show that neither
homogeneous two-edge shape closes the leaf-deck gap at orders eight through
eleven. -/
def neitherHomogeneousTwoEdgeShapeClaim15580 : Prop :=
  treeCount15580 8 = 23 ∧
    treeCount15580 9 = 47 ∧
    treeCount15580 10 = 106 ∧
    treeCount15580 11 = 235 ∧
    Matrix.rank (leafPlusMatchingMatrix15580 8) = 22 ∧
    Matrix.rank (leafPlusMatchingMatrix15580 9) = 46 ∧
    Matrix.rank (leafPlusMatchingMatrix15580 10) = 93 ∧
    Matrix.rank (leafPlusMatchingMatrix15580 11) = 205 ∧
    Matrix.rank (leafPlusPathThreeMatrix15580 8) = 21 ∧
    Matrix.rank (leafPlusPathThreeMatrix15580 9) = 46 ∧
    Matrix.rank (leafPlusPathThreeMatrix15580 10) = 93 ∧
    Matrix.rank (leafPlusPathThreeMatrix15580 11) = 205 ∧
    treeCount15580 8 - Matrix.rank (leafPlusMatchingMatrix15580 8) = 1 ∧
    treeCount15580 9 - Matrix.rank (leafPlusMatchingMatrix15580 9) = 1 ∧
    treeCount15580 10 - Matrix.rank (leafPlusMatchingMatrix15580 10) = 13 ∧
    treeCount15580 11 - Matrix.rank (leafPlusMatchingMatrix15580 11) = 30 ∧
    treeCount15580 8 - Matrix.rank (leafPlusPathThreeMatrix15580 8) = 2 ∧
    treeCount15580 9 - Matrix.rank (leafPlusPathThreeMatrix15580 9) = 1 ∧
    treeCount15580 10 - Matrix.rank (leafPlusPathThreeMatrix15580 10) = 13 ∧
    treeCount15580 11 - Matrix.rank (leafPlusPathThreeMatrix15580 11) = 30

end MathlibPlus.Open.ResearchFormalization.O0352
