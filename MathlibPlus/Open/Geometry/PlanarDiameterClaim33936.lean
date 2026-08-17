import MathlibPlus.Open.Geometry.PlanarRhombicCore33947

namespace MathlibPlus.Open.Geometry.PlanarDiameterClaim33936

open MathlibPlus.Open.Geometry.PlanarRhombicCore33947

noncomputable section

/-- The set of endpoints of all diameter pairs. -/
def diameterEndpointSet33936 {n : ℕ}
    (X : Configuration n) : Finset (Fin n) :=
  (diameterPairs X).biUnion (fun p => {p.1.1, p.1.2})

/-- A pair of disjoint diameter edges crosses exactly once in their interiors. -/
def interiorSegmentsMeetExactlyOnce33936 {n : ℕ}
    (X : Configuration n) (p q : PairIndex n) : Prop :=
  ∃! z : Point,
    z ∈ openSegment (X p.1.1) (X p.1.2) ∧
      z ∈ openSegment (X q.1.1) (X q.1.2)

/-- Two non-disjoint diameter edges meet only at their shared endpoint. -/
def sharedEndpointOnly33936 {n : ℕ}
    (X : Configuration n) (p q : PairIndex n) : Prop :=
  ∃ i : Fin n,
    ((i = p.1.1 ∨ i = p.1.2) ∧
      (i = q.1.1 ∨ i = q.1.2)) ∧
      ∀ z : Point,
        z ∈ closedSegment (X p.1.1) (X p.1.2) ∧
          z ∈ closedSegment (X q.1.1) (X q.1.2) →
          z = X i

/-- The planar diameter graph is a linear thrackle. -/
def diameterGraphLinearThrackle33936 {n : ℕ}
    (X : Configuration n) : Prop :=
  ∀ p ∈ diameterPairs X, ∀ q ∈ diameterPairs X, p ≠ q →
    (disjointPairEndpoints p q →
      interiorSegmentsMeetExactlyOnce33936 X p q) ∧
    (¬ disjointPairEndpoints p q → sharedEndpointOnly33936 X p q)

/-- Every diameter endpoint is a hull vertex. -/
def everyDiameterEndpointIsHullVertex33936 {n : ℕ}
    (X : Configuration n) : Prop :=
  ∀ i ∈ diameterEndpointSet33936 X, hullVertex X i

/-- Claim 33936: the global planar minimizer carrier gives the linear
thrackle, diameter-edge/hull bound, and the exact closest-edge lower-bound
chain through the global grid hull bound. -/
def diameterEdgeAndClosestEdgeBounds_claim33936 : Prop :=
  ∀ (n : ℕ) (X : Configuration n),
    firstOrderIsolatedGlobalDiameterMinimizer X →
    triangleFreeContact X →
      diameterGraphLinearThrackle33936 X ∧
        everyDiameterEndpointIsHullVertex33936 X ∧
        diameterCount X ≤ hullCount X ∧
        hullCount X ≤ hullBound n ∧
        2 * n - 2 - hullBound n ≤
          2 * n - 2 - hullCount X ∧
        2 * n - 2 - hullCount X ≤ contactCount X

end

end MathlibPlus.Open.Geometry.PlanarDiameterClaim33936
