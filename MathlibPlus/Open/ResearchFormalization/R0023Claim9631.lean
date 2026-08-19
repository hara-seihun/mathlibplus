import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0023Claim9631

noncomputable section

/-- Claim 9631: an orthogonal Euclidean coordinate transport preserves
point-to-set distance.  The source identity is valid for every set, so the
lattice carrier is retained as a `Set` without inventing a separate lattice
encoding. -/
def orthogonalTransportPreservesPointToLatticeDistance_claim9631 : Prop :=
  ∀ (n : ℕ)
    (lattice : Set (EuclideanSpace ℝ (Fin n)))
    (orthogonal : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin n))
    (point : EuclideanSpace ℝ (Fin n)),
    Metric.infDist (orthogonal point) (orthogonal '' lattice) =
      Metric.infDist point lattice

end

end MathlibPlus.Open.ResearchFormalization.R0023Claim9631
