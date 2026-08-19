import MathlibPlus.Open.Graphs.BasisTranspose
import MathlibPlus.Open.Research.FormalizationR0375

namespace MathlibPlus.Open.ResearchFormalization.C0287Claim4015

open MathlibPlus.Open.Graphs
open MathlibPlus.Open.Research.R0375

noncomputable section

/-- A graph type represented by a graph on `Fin n` with no isolated vertices. -/
def noIsolatedGraphType {n : ℕ} (G : GraphIsoClass n) : Prop :=
  ∀ v : Fin n, ∃ w : Fin n, (graphRepresentative G).Adj v w

abbrev spanningGraphType (n : ℕ) :=
  {G : GraphIsoClass n // noIsolatedGraphType G}

/-- The number of edge-subgraph copies of the type `Y` in the type `X`. -/
noncomputable def spanningCount {n : ℕ}
    (Y X : spanningGraphType n) : ℕ :=
  spanningSubgraphCount n (graphRepresentative Y.1) (graphRepresentative X.1)

/-- The edge count of a graph isomorphism type. -/
noncomputable def graphTypeEdgeCount {n : ℕ} (X : spanningGraphType n) : ℕ :=
  edgeCount (graphRepresentative X.1)

/-- Claim 4015: the maximum-edge spanning type is the host type, and the full
vector of actual spanning-subgraph counts identifies the graph type. -/
def claim4015_spanningCountsIdentifyGraphByMaximumEdgeCount : Prop :=
  ∀ n : ℕ,
    (∀ (X Y : spanningGraphType n),
      spanningCount Y X > 0 →
        graphTypeEdgeCount Y ≤ graphTypeEdgeCount X) ∧
    (∀ (X Y : spanningGraphType n),
      spanningCount Y X > 0 →
        graphTypeEdgeCount Y = graphTypeEdgeCount X → Y = X) ∧
    (∀ (X X' : spanningGraphType n),
      (∀ Y : spanningGraphType n,
        spanningCount Y X = spanningCount Y X') → X = X')

end

end MathlibPlus.Open.ResearchFormalization.C0287Claim4015
