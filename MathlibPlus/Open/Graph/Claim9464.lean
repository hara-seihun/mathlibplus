import MathlibPlus.Open.Graph.AdmittedClaim9463
import MathlibPlus.Open.Graph.MinimumStarEquality9465
import MathlibPlus.Open.GraphReconstruction.StarFirstPairs
import MathlibPlus.Open.Research.FormalizationBatchDecks

namespace MathlibPlus.Open.Graph.Claim9464

noncomputable section
open Classical

/-- A graph-isomorphism class of a finite simple graph, with its finite
vertex-card retained so classes of different orders can be paired. -/
abbrev FiniteGraphClass :=
  Σ n : ℕ, MathlibPlus.Open.ResearchFormalizationBatch.DeckGraphClass n

noncomputable def finiteGraphClassOf {V : Type*} [Fintype V]
    (G : SimpleGraph V) : FiniteGraphClass :=
  let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  ⟨Fintype.card V,
    MathlibPlus.Open.ResearchFormalizationBatch.deckClass
      (SimpleGraph.comap (e : Fin (Fintype.card V) → V) G)⟩

/-- The spanning graph on the ambient vertex carrier with edge set `A`. -/
def edgePartGraph {V : Type*} (A : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (A : Set (Sym2 V))

noncomputable def edgePartType {V : Type*} [Fintype V]
    (A : Finset (Sym2 V)) : FiniteGraphClass :=
  finiteGraphClassOf (edgePartGraph A)

/-- The type of the spanning vertex-deleted graph `Y - v`. -/
noncomputable def deletedCardType {V : Type*} [Fintype V]
    (Y : SimpleGraph V) (v : V) : FiniteGraphClass :=
  finiteGraphClassOf (MathlibPlus.Open.GraphReconstruction.deleteVertex Y v)

noncomputable def thetaPair {V : Type*} [Fintype V] (Y : SimpleGraph V)
    (A : Finset (Sym2 V)) : FiniteGraphClass × FiniteGraphClass :=
  (edgePartType A, edgePartType (Y.edgeFinset \ A))

/-- The complementary-pair invariant, retaining one multiset entry for every
valid distinct edge subset and grading it by the selected-edge cardinality. -/
def thetaGraded {V : Type*} [Fintype V] [DecidableEq V]
    (Y : SimpleGraph V) :
    Multiset ((FiniteGraphClass × FiniteGraphClass) × ℕ) :=
  (Y.edgeFinset.powerset.filter
    (fun A => MathlibPlus.Open.Graph.AdmittedClaim9463.validPart Y A)).val.map
    (fun A => (thetaPair Y A, A.card))

def thetaLayer {V : Type*} [Fintype V] [DecidableEq V]
    (Y : SimpleGraph V) (d : ℕ) :
    Multiset ((FiniteGraphClass × FiniteGraphClass) × ℕ) :=
  (thetaGraded Y).filter (fun x => x.2 = d)

/-- The least vertex representing a given edge-star; this realizes the
admitted distinct-star multiplicity convention on `Fin n`. -/
def minimumStarRepresentative {n : ℕ} (Y : SimpleGraph (Fin n))
    (v : Fin n) : Prop :=
  ∀ u : Fin n,
    MathlibPlus.Open.Graph.AdmittedClaim9463.edgeStar Y u =
      MathlibPlus.Open.Graph.AdmittedClaim9463.edgeStar Y v →
    v ≤ u

def minimumStarVertices {n : ℕ} (Y : SimpleGraph (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun v =>
    Y.degree v = Y.minDegree ∧ minimumStarRepresentative Y v)

noncomputable def minimumStarLayer {n : ℕ} (Y : SimpleGraph (Fin n)) :
    Multiset ((FiniteGraphClass × FiniteGraphClass) × ℕ) :=
  (minimumStarVertices Y).val.map (fun v =>
    ((edgePartType
        (MathlibPlus.Open.Graph.AdmittedClaim9463.edgeStar Y v),
      deletedCardType Y v), Y.degree v))

noncomputable def minimumDegreeCardMultiset {n : ℕ}
    (Y : SimpleGraph (Fin n)) : Multiset FiniteGraphClass :=
  (minimumStarVertices Y).val.map (deletedCardType Y)

noncomputable def thetaMinimumGrade {n : ℕ} (Y : SimpleGraph (Fin n)) : ℕ :=
  sInf {d : ℕ | ∃ x ∈ thetaGraded Y, x.2 = d}

/-- Claim 9464: the graded complementary-pair multiset has the exact
minimum layer of distinct minimum-degree vertex stars, and its minimum grade
and card projection recover the minimum degree and the minimum-degree cards. -/
def claim9464 : Prop :=
  ∀ {n : ℕ} (Y : SimpleGraph (Fin n)),
    MathlibPlus.Open.Graph.hasNoIsolatedVertices Y →
    MathlibPlus.Open.Graph.isNotComplete Y →
    thetaLayer Y Y.minDegree = minimumStarLayer Y ∧
      thetaMinimumGrade Y = Y.minDegree ∧
      (thetaLayer Y Y.minDegree).map (fun x => x.1.2) =
        minimumDegreeCardMultiset Y ∧
      (∀ v : Fin n, Y.degree v = Y.minDegree →
        MathlibPlus.Open.GraphReconstruction.isomorphicToKOneD
          (MathlibPlus.Open.GraphReconstruction.starSubgraph Y v)
          Y.minDegree)

end

end MathlibPlus.Open.Graph.Claim9464
