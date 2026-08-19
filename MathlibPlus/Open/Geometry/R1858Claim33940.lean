import MathlibPlus.Open.Geometry.PlanarRhombicCore33947

namespace MathlibPlus.Open.Geometry.PlanarClaim33940

open MathlibPlus.Open.Geometry.PlanarRhombicCore33947

noncomputable section

/-- The exact component-indexed face-excess and quadrilateral-count chain on
 the normalized global-minimizer planar contact carrier. -/
def faceExcessInequality_claim33940 : Prop :=
  ∀ (n f : ℕ) (X : Configuration n)
    (rotation : Fin n → List (Dart n))
    (faces : Fin f → List (List (Dart n)))
    (regions : Fin f → Set Point) (outer : Fin f),
    firstOrderIsolatedGlobalDiameterMinimizer X →
    triangleFreeContact X →
    straightLinePlaneContactEmbedding X rotation faces regions outer →
      (boundedFaceCount outer : ℤ) =
          (contactCount X : ℤ) - (n : ℤ) +
            (contactComponentCount X : ℤ) ∧
      (∀ F : Fin f, F ≠ outer → 4 ≤ faceDegree faces F) ∧
      boundedFaceDegreeSum faces outer ≤ 2 * contactCount X ∧
      hullCount X ≤ hullBound n ∧
      2 * n - 2 - hullCount X ≤ contactCount X ∧
      1 ≤ contactComponentCount X ∧
      (faceExcess faces outer : ℤ) ≤
        2 * (contactCount X : ℤ) -
          4 * ((contactCount X : ℤ) - (n : ℤ) +
            (contactComponentCount X : ℤ)) ∧
      2 * (contactCount X : ℤ) -
          4 * ((contactCount X : ℤ) - (n : ℤ) +
            (contactComponentCount X : ℤ)) =
        4 * (n : ℤ) - 2 * (contactCount X : ℤ) -
          4 * (contactComponentCount X : ℤ) ∧
      (faceExcess faces outer : ℤ) ≤
        4 * (n : ℤ) - 2 * (contactCount X : ℤ) -
          4 * (contactComponentCount X : ℤ) ∧
      (faceExcess faces outer : ℤ) ≤
        4 + 2 * (hullCount X : ℤ) -
          4 * (contactComponentCount X : ℤ) ∧
      4 + 2 * (hullCount X : ℤ) -
          4 * (contactComponentCount X : ℤ) ≤
        2 * (hullCount X : ℤ) ∧
      (faceExcess faces outer : ℤ) ≤ 2 * (hullCount X : ℤ) ∧
      nonQuadrilateralFaceCount faces outer ≤ 2 * hullCount X ∧
      quadrilateralFaceCount faces outer ≥
        n - 1 - 3 * hullCount X ∧
      quadrilateralFaceCount faces outer ≥ n - 1 - 3 * hullBound n

end

end MathlibPlus.Open.Geometry.PlanarClaim33940
