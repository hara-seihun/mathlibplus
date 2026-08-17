import MathlibPlus.Open.ResearchFormalization.BatchGraph_01a0040167a37f8a848e6f8a61d

namespace MathlibPlus.Open.ResearchFormalization.Batch_01a0040167a37f8a848e6f8a61d

noncomputable section

private def eligibleDemand {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A : Set V) (u v : V) : Prop :=
  u ≠ v ∧ graphSameSide A u v ∧
    Disjoint (crossingNeighbors G A u) (crossingNeighbors G A v)

private def normalizedCrossingDegree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A C : Set V) (v : V) : ℝ :=
  (crossingDegreeNat G A v : ℝ) / (C.ncard : ℝ)

private def thresholdWeight (t z : ℝ) : ℝ :=
  if z < t then 1 else if z ≤ 1 - t then 1 / 2 else 0

/-- Claim 16868: the three-level threshold profile on demand-active
vertices is a fractional vertex cover for every codegree-zero demand, and
eligible endpoints have normalized crossing degrees summing to at most one. -/
def claim16868 : Prop :=
  ∀ {V : Type*} [Fintype V] (G : SimpleGraph V) (A B : Set V),
    cutHypotheses G A B →
      ∀ (t : ℝ), 0 ≤ t → t ≤ 1 / 2 →
        ∀ (C D : Set V),
          (C = A ∧ D = B) ∨ (C = B ∧ D = A) →
          ∀ (u v : V), eligibleDemand G A u v →
            u ∈ C → v ∈ C →
            normalizedCrossingDegree G A D u +
                normalizedCrossingDegree G A D v ≤ 1 ∧
              thresholdWeight t (normalizedCrossingDegree G A D u) +
                  thresholdWeight t (normalizedCrossingDegree G A D v) ≥ 1

end

end MathlibPlus.Open.ResearchFormalization.Batch_01a0040167a37f8a848e6f8a61d
