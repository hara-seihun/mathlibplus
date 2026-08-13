import Mathlib

namespace MathlibPlus.GraphTheory.Claim9482

/-- The set of host edges incident with a vertex in the finite edge-set model. -/
def incidentEdgeSet_claim9482
    {Vertex : Type*} [DecidableEq Vertex]
    (edges : Finset (Finset Vertex)) (vertex : Vertex) :
    Finset (Finset Vertex) :=
  edges.filter fun edge => vertex ∈ edge

/-- A finite edge set is simple when each edge has exactly two vertices. -/
def IsSimpleEdgeSet_claim9482
    {Vertex : Type*} [DecidableEq Vertex]
    (edges : Finset (Finset Vertex)) : Prop :=
  ∀ edge ∈ edges, edge.card = 2

/-- Every vertex is incident with at least one host edge. -/
def HasNoIsolatedVertices_claim9482
    {Vertex : Type*} [DecidableEq Vertex]
    (edges : Finset (Finset Vertex)) : Prop :=
  ∀ vertex, (incidentEdgeSet_claim9482 edges vertex).Nonempty

/-- The degree of a vertex in the finite edge-set model. -/
def vertexDegree_claim9482
    {Vertex : Type*} [DecidableEq Vertex]
    (edges : Finset (Finset Vertex)) (vertex : Vertex) : ℕ :=
  (incidentEdgeSet_claim9482 edges vertex).card

/-- Every selected edge contains the displayed star center. -/
def IsStarCentered_claim9482
    {Vertex : Type*}
    (part : Finset (Finset Vertex)) (center : Vertex) : Prop :=
  ∀ edge ∈ part, center ∈ edge

/-- The complement misses a vertex when every host edge incident with it is selected. -/
def ComplementMissesVertex_claim9482
    {Vertex : Type*} [DecidableEq Vertex]
    (edges part : Finset (Finset Vertex)) (vertex : Vertex) : Prop :=
  incidentEdgeSet_claim9482 edges vertex ⊆ part

/-- The selected part is the full star of some host vertex. -/
def IsCardStarPart_claim9482
    {Vertex : Type*} [DecidableEq Vertex]
    (edges part : Finset (Finset Vertex)) : Prop :=
  ∃ vertex, part = incidentEdgeSet_claim9482 edges vertex

/-- Every valid star part in a layer is a full vertex star. -/
def StarLayerPureAt_claim9482
    {Vertex : Type*} [DecidableEq Vertex]
    (edges : Finset (Finset Vertex)) (degree : ℕ) : Prop :=
  ∀ part center missed,
    part ⊆ edges →
    part.card = degree →
    IsStarCentered_claim9482 part center →
    ComplementMissesVertex_claim9482 edges part missed →
    IsCardStarPart_claim9482 edges part

private theorem edge_eq_pair_of_simple
    {Vertex : Type*} [DecidableEq Vertex]
    {edges : Finset (Finset Vertex)}
    (simple : IsSimpleEdgeSet_claim9482 edges)
    {edge : Finset Vertex} (edgeIn : edge ∈ edges)
    {first second : Vertex}
    (firstIn : first ∈ edge) (secondIn : second ∈ edge)
    (distinct : first ≠ second) :
    edge = {first, second} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro vertex vertexIn
    simp only [Finset.mem_insert, Finset.mem_singleton] at vertexIn
    rcases vertexIn with rfl | rfl
    · exact firstIn
    · exact secondIn
  · rw [simple edge edgeIn]
    simp [distinct]

/-- If every vertex has degree at least two, every star layer is pure.

This is the literal finite-edge-set formalization of the minimum-degree-two
corollary in claim 9482. -/
theorem allLayersPureOfMinDegreeTwo_claim9482
    {Vertex : Type*} [DecidableEq Vertex]
    {edges : Finset (Finset Vertex)}
    (simple : IsSimpleEdgeSet_claim9482 edges)
    (noIsolated : HasNoIsolatedVertices_claim9482 edges)
    (minDegree : ∀ vertex, 2 ≤ vertexDegree_claim9482 edges vertex) :
    ∀ degree, StarLayerPureAt_claim9482 edges degree := by
  intro degree part center missed partSubset _partCard centered complementMisses
  have partSubsetStar :
      part ⊆ incidentEdgeSet_claim9482 edges center := by
    intro edge edgeIn
    exact Finset.mem_filter.mpr ⟨partSubset edgeIn, centered edge edgeIn⟩
  by_cases same : missed = center
  · refine ⟨center, Finset.Subset.antisymm partSubsetStar ?_⟩
    change incidentEdgeSet_claim9482 edges missed ⊆ part at complementMisses
    simpa [same] using complementMisses
  · have incidentSubsetSingleton :
        incidentEdgeSet_claim9482 edges missed ⊆
          ({({missed, center} : Finset Vertex)} : Finset (Finset Vertex)) := by
      intro edge edgeIn
      have edgeInHost : edge ∈ edges :=
        (Finset.mem_filter.mp edgeIn).1
      have missedIn : missed ∈ edge :=
        (Finset.mem_filter.mp edgeIn).2
      have edgeInPart : edge ∈ part := complementMisses edgeIn
      have centerIn : center ∈ edge := centered edge edgeInPart
      have edgeEq := edge_eq_pair_of_simple simple edgeInHost
        missedIn centerIn same
      simpa only [Finset.mem_singleton] using edgeEq
    have pairInIncident :
        ({missed, center} : Finset Vertex) ∈
          incidentEdgeSet_claim9482 edges missed := by
      rcases noIsolated missed with ⟨edge, edgeIn⟩
      have edgeInHost : edge ∈ edges :=
        (Finset.mem_filter.mp edgeIn).1
      have missedIn : missed ∈ edge :=
        (Finset.mem_filter.mp edgeIn).2
      have edgeInPart : edge ∈ part := complementMisses edgeIn
      have centerIn : center ∈ edge := centered edge edgeInPart
      have edgeEq := edge_eq_pair_of_simple simple edgeInHost
        missedIn centerIn same
      simpa [edgeEq] using edgeIn
    have singletonSubsetIncident :
        ({({missed, center} : Finset Vertex)} : Finset (Finset Vertex)) ⊆
          incidentEdgeSet_claim9482 edges missed := by
      intro edge edgeIn
      have edgeEq : edge = ({missed, center} : Finset Vertex) := by
        simpa only [Finset.mem_singleton] using edgeIn
      simpa [edgeEq] using pairInIncident
    have incidentEq :
        incidentEdgeSet_claim9482 edges missed =
          ({({missed, center} : Finset Vertex)} : Finset (Finset Vertex)) :=
      Finset.Subset.antisymm incidentSubsetSingleton singletonSubsetIncident
    have degreeOne : vertexDegree_claim9482 edges missed = 1 := by
      simp [vertexDegree_claim9482, incidentEq]
    have degreeAtLeastTwo := minDegree missed
    omega

end MathlibPlus.GraphTheory.Claim9482
