import MathlibPlus.Open.Geometry.PlanarRhombicCore33947

namespace MathlibPlus.Open.ResearchFormalization.Claim34519

open MathlibPlus.Open.Geometry.PlanarRhombicCore33947

noncomputable section

/-- The planar hull area of the actual configuration carrier. -/
def hullArea34519 {n : ℕ} (X : Configuration n) : ℝ :=
  ENNReal.toReal
    (MeasureTheory.volume (convexHull ℝ (Set.range X)))

/-- Claim 34519: for a normalized diameter-minimizing planar configuration,
the area of its actual convex hull is bounded by the planar isodiametric cap,
which is then bounded by the sharp planar diameter estimate. -/
def claim34519 : Prop :=
  ∀ (n : ℕ) (X : Configuration n),
    normalized X →
    maximumDistance X = minimumDiameter n →
      hullArea34519 X ≤
          Real.pi * (minimumDiameter n) ^ 2 / 4 ∧
        Real.pi * (minimumDiameter n) ^ 2 / 4 ≤
          (Real.sqrt 3 / 2) * (n : ℝ)

end

end MathlibPlus.Open.ResearchFormalization.Claim34519
