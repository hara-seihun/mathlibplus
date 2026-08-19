import MathlibPlus.Open.ResearchFormalization.RhombusDiagonalDefectClaim34526

namespace MathlibPlus.Open.ResearchFormalization.Claim34521

open MathlibPlus.Open.Geometry.PlanarRhombicCore33947

noncomputable section

abbrev FacePoint := MathlibPlus.Open.Geometry.PlanarRhombicCore33947.Point
abbrev FaceConfiguration (n : ℕ) :=
  MathlibPlus.Open.Geometry.PlanarRhombicCore33947.Configuration n
abbrev FaceDart (n : ℕ) :=
  MathlibPlus.Open.Geometry.PlanarRhombicCore33947.Dart n

/-- A triangle in the unit contact graph, expressed using the reviewed
configuration and contact-adjacency carrier. -/
def unitEquilateralTriangle {n : ℕ}
    (X : FaceConfiguration n) (a b c : Fin n) : Prop :=
  contactAdjacent X a b ∧
    contactAdjacent X b c ∧
    contactAdjacent X c a

/-- Claim 34521: supplied unit-rhombus faces have the closed angle interval;
endpoint angles make the corresponding shorter diagonal a unit contact and
produce a unit equilateral triangle.  The triangle-free contact hypothesis
therefore makes every face angle strict. -/
def claim34521 : Prop :=
  ∀ (n f q : ℕ) (X : FaceConfiguration n)
    (rotation : Fin n → List (FaceDart n))
    (faces : Fin f → List (List (FaceDart n)))
    (regions : Fin f → Set FacePoint) (outer : Fin f)
    (face : Fin q → Fin f) (cycles : Fin q → List (FaceDart n))
    (vertices : Fin q → Fin 4 → Fin n),
    normalized X →
    triangleFreeContact X →
    straightLinePlaneContactEmbedding X rotation faces regions outer →
    MathlibPlus.Open.ResearchFormalization.RhombusDiagonalDefectClaim34526.suppliedCycleData
      X faces outer face cycles vertices →
      (∀ F : Fin q,
        Real.pi / 3 ≤
            MathlibPlus.Open.ResearchFormalization.RhombusDiagonalDefectClaim34526.faceAngle
              X vertices F ∧
          MathlibPlus.Open.ResearchFormalization.RhombusDiagonalDefectClaim34526.faceAngle
              X vertices F ≤ 2 * Real.pi / 3 ∧
          (MathlibPlus.Open.ResearchFormalization.RhombusDiagonalDefectClaim34526.faceAngle
              X vertices F = Real.pi / 3 →
            MathlibPlus.Open.ResearchFormalization.RhombusDiagonalDefectClaim34526.shorterDiagonal
                X vertices F = 1 ∧
              pointDistance (X (vertices F 1)) (X (vertices F 3)) = 1 ∧
              unitEquilateralTriangle X (vertices F 0) (vertices F 1)
                (vertices F 3)) ∧
          (MathlibPlus.Open.ResearchFormalization.RhombusDiagonalDefectClaim34526.faceAngle
              X vertices F = 2 * Real.pi / 3 →
            MathlibPlus.Open.ResearchFormalization.RhombusDiagonalDefectClaim34526.shorterDiagonal
                X vertices F = 1 ∧
              pointDistance (X (vertices F 0)) (X (vertices F 2)) = 1 ∧
              unitEquilateralTriangle X (vertices F 0) (vertices F 1)
                (vertices F 2))) ∧
        (∀ F : Fin q,
          Real.pi / 3 <
              MathlibPlus.Open.ResearchFormalization.RhombusDiagonalDefectClaim34526.faceAngle
                X vertices F ∧
            MathlibPlus.Open.ResearchFormalization.RhombusDiagonalDefectClaim34526.faceAngle
                X vertices F < 2 * Real.pi / 3)

end

end MathlibPlus.Open.ResearchFormalization.Claim34521
