import MathlibPlus.Open.ResearchFormalization.RhombusDiagonalDefectClaim34526

namespace MathlibPlus.Open.ResearchFormalization.Claim34523

open scoped BigOperators
open MathlibPlus.Open.Geometry.PlanarRhombicCore33947
open MathlibPlus.Open.ResearchFormalization.RhombusDiagonalDefectClaim34526

noncomputable section

abbrev Point := MathlibPlus.Open.Geometry.PlanarRhombicCore33947.Point
abbrev Configuration (n : ℕ) :=
  MathlibPlus.Open.Geometry.PlanarRhombicCore33947.Configuration n
abbrev Dart (n : ℕ) := MathlibPlus.Open.Geometry.PlanarRhombicCore33947.Dart n

def suppliedFaceAreaBound_claim34523 : Prop :=
  ∀ (n f q : ℕ) (X : Configuration n)
    (rotation : Fin n → List (Dart n))
    (faces : Fin f → List (List (Dart n)))
    (regions : Fin f → Set Point) (outer : Fin f)
    (face : Fin q → Fin f) (cycles : Fin q → List (Dart n))
    (vertices : Fin q → Fin 4 → Fin n),
    normalized X →
    triangleFreeContact X →
    straightLinePlaneContactEmbedding X rotation faces regions outer →
    suppliedCycleData X faces outer face cycles vertices →
    ((∀ F G : Fin q, F ≠ G →
        Disjoint (interior (regions (face F)))
          (interior (regions (face G)))) ∧
      (∀ F : Fin q,
        interior (regions (face F)) ⊆
          convexHull ℝ (Set.range X))) →
    (∑ F : Fin q, Real.sin (faceAngle X vertices F)) ≤
      ENNReal.toReal
        (MeasureTheory.volume (convexHull ℝ (Set.range X)))

end

end MathlibPlus.Open.ResearchFormalization.Claim34523
