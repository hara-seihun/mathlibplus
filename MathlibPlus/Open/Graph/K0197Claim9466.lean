import MathlibPlus.Open.Graph.Claim9464

namespace MathlibPlus.Open.Graph.K0197Claim9466

open MathlibPlus.Open.Graph.Claim9464
open MathlibPlus.Open.Graph.AdmittedClaim9463
open Classical

noncomputable section

/-- The star/card part of the layer immediately above minimum degree. -/
noncomputable def degreePlusOneStarLayer9466 {n : ℕ}
    (Y : SimpleGraph (Fin n)) :
    Multiset ((FiniteGraphClass × FiniteGraphClass) × ℕ) :=
  (Finset.univ.filter
      (fun v : Fin n => Y.degree v = Y.minDegree + 1)).val.map
    (fun v =>
      ((edgePartType
          (MathlibPlus.Open.Graph.AdmittedClaim9463.edgeStar Y v),
        deletedCardType Y v),
        Y.minDegree + 1))

/-- The degree-minimum star with one nonincident edge added. -/
noncomputable def degreeStarPlusEdgeLayer9466 {n : ℕ}
    (Y : SimpleGraph (Fin n)) :
    Multiset ((FiniteGraphClass × FiniteGraphClass) × ℕ) :=
  (Finset.univ.filter
      (fun v : Fin n => Y.degree v = Y.minDegree)).val.bind
    (fun v =>
      ((MathlibPlus.Open.GraphReconstruction.deleteVertex Y v).edgeFinset).val.map (fun e =>
        ((edgePartType
            (MathlibPlus.Open.Graph.AdmittedClaim9463.edgeStar Y v ∪ {e}),
          edgePartType
            ((MathlibPlus.Open.GraphReconstruction.deleteVertex Y v).edgeFinset \ {e})),
          Y.minDegree + 1)))

/-- Claim 9466: the next graded layer is the exact multiset union of the
larger minimum-degree stars and the minimum-degree star-plus-edge pairs. -/
def exactLayerImmediatelyAboveMinimumDegree_claim9466 : Prop :=
  ∀ {n : ℕ} (Y : SimpleGraph (Fin n)),
    MathlibPlus.Open.Graph.hasNoIsolatedVertices Y →
      MathlibPlus.Open.Graph.isNotComplete Y →
        thetaLayer Y (Y.minDegree + 1) =
          degreePlusOneStarLayer9466 Y + degreeStarPlusEdgeLayer9466 Y

end

end MathlibPlus.Open.Graph.K0197Claim9466
