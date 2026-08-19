import MathlibPlus.Open.Graphs.BasisTranspose
import MathlibPlus.Open.Research.GraphReconstructionExact

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.C0287Claim4019

open MathlibPlus.Open.Graphs
open MathlibPlus.Open.Research.GraphReconstructionExact

noncomputable section

/-- A graph type represented by a graph on `Fin n` with no isolated vertices. -/
def noIsolatedGraphType {n : ℕ} (G : GraphIsoClass n) : Prop :=
  ∀ v : Fin n, ∃ w : Fin n, (graphRepresentative G).Adj v w

abbrev spanningGraphType (n : ℕ) :=
  {G : GraphIsoClass n // noIsolatedGraphType G}

/-- The proper graph types on two or three vertices, the two possible orders
strictly below four in the order-four covering system. -/
abbrev properSmallGraphType :=
  Σ q : Fin 2, {G : GraphIsoClass (q.1 + 2) // noIsolatedGraphType G}

/-- The representative graph of a proper small graph type. -/
noncomputable def smallGraph (F : properSmallGraphType) :
    SimpleGraph (Fin (F.1.1 + 2)) :=
  graphRepresentative F.2.1

/-- The order-two and order-three covering families used at order four. -/
abbrev kocayRow :=
  Σ k : Fin 2, Fin (k.1 + 2) → properSmallGraphType

/-- The number of ordered tuples of subgraphs of `Y` of the prescribed types
whose edge union is all of `Y`. -/
noncomputable def orderedCoverCount
    (F : kocayRow) (Y : spanningGraphType 4) : ℕ :=
  let G := graphRepresentative Y.1
  let candidates : Type :=
    ∀ i : Fin (F.1.1 + 2), G.Subgraph
  let covered : candidates → Prop := fun A =>
    (∀ i, Nonempty (smallGraph (F.2 i) ≃g (A i).coe)) ∧
      (⋃ i, (A i).edgeSet) = G.edgeSet
  letI : Fintype {A : candidates // covered A} := Fintype.ofFinite _
  Fintype.card {A : candidates // covered A}

/-- The actual Kocay covering matrix for the order-four two- and three-part
families. -/
noncomputable def coveringMatrix :
    Matrix kocayRow (spanningGraphType 4) ℚ :=
  fun F Y => orderedCoverCount F Y

/-- Claim 4019: the order-four covering matrix has its 36 actual Kocay rows,
seven actual spanning-type columns, full rank, zero deficiency on that
matrix, and the resulting order-four reconstruction consequence. -/
def claim4019_exactRankOrderFour : Prop :=
  letI : Fintype properSmallGraphType := Fintype.ofFinite _
  letI : Fintype (spanningGraphType 4) := Fintype.ofFinite _
  letI : Fintype kocayRow := Fintype.ofFinite _
  let M := coveringMatrix
  Fintype.card (spanningGraphType 4) = 7 ∧
    Fintype.card kocayRow = 36 ∧
      Matrix.rank M = 7 ∧
        Fintype.card (spanningGraphType 4) - Matrix.rank M = 0 ∧
          vertexReconstructibleAt 3

end

end MathlibPlus.Open.ResearchFormalization.C0287Claim4019
