import MathlibPlus.Open.ResearchFormalization.GraphClaims01a00bdd

namespace MathlibPlus.Open.ResearchFormalization.GraphDeckCommutators14320

open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization.GraphClaims01a00bdd

abbrev GraphSpace14320 (n : ℕ) := LabelledGraphSpace14320 n

noncomputable def vertexDeckOnBasis14320 {n : ℕ}
    (G : LabelledGraph14320 n) : GraphSpace14320 (n - 1) :=
  ∑ v : Fin n,
    Finsupp.single (deleteVertex14320 G v) (1 : ℚ)

noncomputable def vertexDeck14320 (n : ℕ) :
    GraphSpace14320 n →ₗ[ℚ] GraphSpace14320 (n - 1) :=
  Finsupp.lift (GraphSpace14320 (n - 1)) ℚ (LabelledGraph14320 n)
    (vertexDeckOnBasis14320)

noncomputable def edgePositions14320 {n : ℕ}
    (G : LabelledGraph14320 n) : Finset (Sym2 (Fin n)) :=
  @Finset.filter _ (fun e => e ∈ G.edgeSet)
    (fun e => Classical.propDecidable (e ∈ G.edgeSet)) Finset.univ

noncomputable def nonedgePositions14320 {n : ℕ}
    (G : LabelledGraph14320 n) : Finset (Sym2 (Fin n)) :=
  @Finset.filter _ (fun e => e ∉ Sym2.diagSet ∧ e ∉ G.edgeSet)
    (fun e => Classical.propDecidable (e ∉ Sym2.diagSet ∧ e ∉ G.edgeSet)) Finset.univ

noncomputable def edgeDeletionOnBasis14320 {n : ℕ}
    (G : LabelledGraph14320 n) : GraphSpace14320 n :=
  (edgePositions14320 G).sum (fun e =>
    Finsupp.single (G.deleteEdges ({e} : Set (Sym2 (Fin n)))) (1 : ℚ))

noncomputable def edgeDeletion14320 (n : ℕ) :
    GraphSpace14320 n →ₗ[ℚ] GraphSpace14320 n :=
  Finsupp.lift (GraphSpace14320 n) ℚ (LabelledGraph14320 n)
    (edgeDeletionOnBasis14320)

noncomputable def edgeAdditionOnBasis14320 {n : ℕ}
    (G : LabelledGraph14320 n) : GraphSpace14320 n :=
  (nonedgePositions14320 G).sum (fun e =>
    Finsupp.single
      (G ⊔ SimpleGraph.fromEdgeSet ({e} : Set (Sym2 (Fin n)))) (1 : ℚ))

noncomputable def edgeAddition14320 (n : ℕ) :
    GraphSpace14320 n →ₗ[ℚ] GraphSpace14320 n :=
  Finsupp.lift (GraphSpace14320 n) ℚ (LabelledGraph14320 n)
    (edgeAdditionOnBasis14320)

noncomputable def degreeWeightedDeckLinear14320 (n : ℕ) :
    GraphSpace14320 n →ₗ[ℚ] GraphSpace14320 (n - 1) :=
  Finsupp.lift (GraphSpace14320 (n - 1)) ℚ (LabelledGraph14320 n)
    (degreeWeightedDeckOnBasis14320)

/-- The vertex deck is the linear extension of the full vertex-deletion sum. -/
def claim19918 : Prop :=
  ∀ (n : ℕ) (G : LabelledGraph14320 n),
    vertexDeck14320 n (Finsupp.single G (1 : ℚ)) =
      ∑ v : Fin n,
        Finsupp.single (deleteVertex14320 G v) (1 : ℚ)

/-- The edge-deletion commutator is the degree-weighted vertex deck. -/
def claim19921 : Prop :=
  ∀ (n : ℕ),
    (vertexDeck14320 n).comp (edgeDeletion14320 n) -
        (edgeDeletion14320 (n - 1)).comp (vertexDeck14320 n) =
      degreeWeightedDeckLinear14320 n

/-- The edge-addition commutator has the order-dependent scalar term and the
 degree-weighted vertex deck as its defect. -/
def claim19922 : Prop :=
  ∀ (n : ℕ),
    (vertexDeck14320 n).comp (edgeAddition14320 n) -
        (edgeAddition14320 (n - 1)).comp (vertexDeck14320 n) =
      ((n - 1 : ℕ) : ℚ) • vertexDeck14320 n -
        degreeWeightedDeckLinear14320 n

end MathlibPlus.Open.ResearchFormalization.GraphDeckCommutators14320
