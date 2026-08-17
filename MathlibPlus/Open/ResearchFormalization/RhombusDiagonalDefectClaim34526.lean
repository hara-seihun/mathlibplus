import MathlibPlus.Open.Geometry.PlanarRhombicCore33947

namespace MathlibPlus.Open.ResearchFormalization.RhombusDiagonalDefectClaim34526

open scoped BigOperators
open Classical
open MathlibPlus.Open.Geometry.PlanarRhombicCore33947

noncomputable section

abbrev Point := MathlibPlus.Open.Geometry.PlanarRhombicCore33947.Point
abbrev Configuration (n : ℕ) :=
  MathlibPlus.Open.Geometry.PlanarRhombicCore33947.Configuration n
abbrev Dart (n : ℕ) := MathlibPlus.Open.Geometry.PlanarRhombicCore33947.Dart n

def rhombusAngle (_a b d : Point) : ℝ :=
  Real.arccos (1 - pointDistance b d ^ 2 / 2)

def faceAngle {n q : ℕ} (X : Configuration n)
    (vertices : Fin q → Fin 4 → Fin n) (F : Fin q) : ℝ :=
  rhombusAngle (X (vertices F 0)) (X (vertices F 1)) (X (vertices F 3))

def shorterDiagonal {n q : ℕ} (X : Configuration n)
    (vertices : Fin q → Fin 4 → Fin n) (F : Fin q) : ℝ :=
  min (pointDistance (X (vertices F 0)) (X (vertices F 2)))
    (pointDistance (X (vertices F 1)) (X (vertices F 3)))

def angularDefect (θ : ℝ) : ℝ :=
  min (θ - Real.pi / 3) (2 * Real.pi / 3 - θ)

def angularBudget {n q : ℕ} (X : Configuration n)
    (vertices : Fin q → Fin 4 → Fin n) (h : ℕ) : Prop :=
  ∑ F : Fin q, angularDefect (faceAngle X vertices F) ≤
    Real.sqrt 3 * (1 + 3 * (h : ℝ)) /
      (2 * ((6 / Real.pi) * (1 - Real.sqrt 3 / 2)))

def suppliedCycleData {n f q : ℕ} (X : Configuration n)
    (faces : Fin f → List (List (Dart n))) (outer : Fin f)
    (face : Fin q → Fin f) (cycles : Fin q → List (Dart n))
    (vertices : Fin q → Fin 4 → Fin n) : Prop :=
  (∀ F : Fin q, isQuadrilateralFace faces outer (face F)) ∧
    (∀ F G : Fin q, face F = face G → F = G) ∧
    (∀ F : Fin f, isQuadrilateralFace faces outer F →
      ∃ G : Fin q, face G = F) ∧
    (∀ F : Fin q, faces (face F) = [cycles F]) ∧
    (∀ F : Fin q, (cycles F).length = 4) ∧
    (∀ F : Fin q,
      cycleVertices (cycles F) =
        [vertices F 0, vertices F 1, vertices F 2, vertices F 3]) ∧
    (∀ F : Fin q, exactUnitRhombusCycle X (cycles F))

def suppliedFaceAreaData {n f q : ℕ} (X : Configuration n)
    (faces : Fin f → List (List (Dart n))) (outer : Fin f)
    (face : Fin q → Fin f) (regions : Fin f → Set Point)
    (vertices : Fin q → Fin 4 → Fin n) : Prop :=
  (∀ F G : Fin q, F ≠ G →
    Disjoint (interior (regions (face F))) (interior (regions (face G)))) ∧
    (∀ F : Fin q,
      interior (regions (face F)) ⊆
        convexHull ℝ (Set.range X)) ∧
    (∑ F : Fin q, Real.sin (faceAngle X vertices F)) ≤
      ENNReal.toReal (MeasureTheory.volume (convexHull ℝ (Set.range X)))

def strictFaceAngles {n q : ℕ} (X : Configuration n)
    (vertices : Fin q → Fin 4 → Fin n) : Prop :=
  ∀ F : Fin q,
    Real.pi / 3 < faceAngle X vertices F ∧
      faceAngle X vertices F < 2 * Real.pi / 3

/-- Claim 34526: the shorter-diagonal formula, its pointwise defect
comparison, and the boundary-order square-root budget. -/
def claim34526 : Prop :=
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
    let s := fun F : Fin q => shorterDiagonal X vertices F
    let c₀ := (6 / Real.pi) * (1 - Real.sqrt 3 / 2)
    (∀ F : Fin q,
      s F = 2 * Real.sin (Real.pi / 6 + δ F / 2) ∧
        0 < s F - 1 ∧ s F - 1 ≤ δ F) ∧
      (∑ F : Fin q, s F - 1) ≤ ∑ F : Fin q, δ F ∧
      angularBudget X vertices h ∧
      (∀ C : ℝ, 0 ≤ C → (h : ℝ) ≤ C * Real.sqrt (n : ℝ) →
        (∑ F : Fin q, s F - 1) ≤
          Real.sqrt 3 * (1 + 3 * C) / (2 * c₀) *
            Real.sqrt (n : ℝ))

end

end MathlibPlus.Open.ResearchFormalization.RhombusDiagonalDefectClaim34526
