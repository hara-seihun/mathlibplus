import MathlibPlus.Open.ResearchFormalization.RhombusDiagonalDefectClaim34526

namespace MathlibPlus.Open.ResearchFormalization.RhombusAngularDefectClaim34525

open scoped BigOperators
open Classical
open MathlibPlus.Open.Geometry.PlanarRhombicCore33947
open MathlibPlus.Open.ResearchFormalization.RhombusDiagonalDefectClaim34526

noncomputable section

abbrev Point := MathlibPlus.Open.Geometry.PlanarRhombicCore33947.Point
abbrev Configuration (n : ℕ) :=
  MathlibPlus.Open.Geometry.PlanarRhombicCore33947.Configuration n
abbrev Dart (n : ℕ) := MathlibPlus.Open.Geometry.PlanarRhombicCore33947.Dart n

/-- Claim 34525: the concavity lower bound for each supplied rhombus angle and
its resulting total angular-defect budget. -/
def claim34525 : Prop :=
  ∀ (n f q h : ℕ) (X : Configuration n)
    (rotation : Fin n → List (Dart n))
    (faces : Fin f → List (List (Dart n)))
    (regions : Fin f → Set Point) (outer : Fin f)
    (face : Fin q → Fin f) (cycles : Fin q → List (Dart n))
    (vertices : Fin q → Fin 4 → Fin n),
    firstOrderIsolatedGlobalDiameterMinimizer X →
    triangleFreeContact X →
    straightLinePlaneContactEmbedding X rotation faces regions outer →
    0 < n →
    h = hullCount X →
    q = quadrilateralFaceCount faces outer →
    (q : ℝ) ≥ (n : ℝ) - 1 - 3 * (h : ℝ) →
    suppliedCycleData X faces outer face cycles vertices →
    suppliedFaceAreaData X faces outer face regions vertices →
    strictFaceAngles X vertices →
    let δ := fun F : Fin q => angularDefect (faceAngle X vertices F)
    let c₀ := (6 / Real.pi) * (1 - Real.sqrt 3 / 2)
    (∀ F : Fin q,
      Real.sin (Real.pi / 3 + δ F) - Real.sqrt 3 / 2 ≥ c₀ * δ F) ∧
      (∑ F : Fin q, δ F) ≤
        Real.sqrt 3 * (1 + 3 * (h : ℝ)) / (2 * c₀)

end

end MathlibPlus.Open.ResearchFormalization.RhombusAngularDefectClaim34525
