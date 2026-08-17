import Mathlib

namespace MathlibPlus.Open.Geometry.PlanarUnitRhombus33943

open scoped BigOperators
open Classical Bornology

noncomputable section

abbrev Point := ℝ × ℝ
abbrev Configuration (n : ℕ) := Fin n → Point
abbrev PairIndex (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev Dart (n : ℕ) := PairIndex n × Bool

 def pointDistance (p q : Point) : ℝ :=
  Real.sqrt ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2)

def inner2 (u v : Point) : ℝ :=
  u.1 * v.1 + u.2 * v.2

def rotate90 (u : Point) : Point :=
  (-u.2, u.1)

def pairDistance {n : ℕ} (X : Configuration n) (p : PairIndex n) : ℝ :=
  pointDistance (X p.1.1) (X p.1.2)

def minimumDistance {n : ℕ} (X : Configuration n) : ℝ :=
  sInf (Set.range (pairDistance X))

def maximumDistance {n : ℕ} (X : Configuration n) : ℝ :=
  sSup (Set.range (pairDistance X))

def unitSeparated {n : ℕ} (X : Configuration n) : Prop :=
  ∀ p : PairIndex n, 1 ≤ pairDistance X p

def normalized {n : ℕ} (X : Configuration n) : Prop :=
  2 ≤ n ∧ Function.Injective X ∧ unitSeparated X ∧ minimumDistance X = 1

def ratio {n : ℕ} (X : Configuration n) : ℝ :=
  maximumDistance X / minimumDistance X

def configurationDistance {n : ℕ} (X Y : Configuration n) : ℝ :=
  sSup (Set.range (fun i : Fin n => pointDistance (X i) (Y i)))

def localRatioMinimizer {n : ℕ} (X : Configuration n) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ Y : Configuration n, Function.Injective Y →
      configurationDistance X Y < ε → ratio X ≤ ratio Y

def contactPairs {n : ℕ} (X : Configuration n) : Finset (PairIndex n) :=
  Finset.univ.filter (fun p => pairDistance X p = minimumDistance X)

def diameterPairs {n : ℕ} (X : Configuration n) : Finset (PairIndex n) :=
  Finset.univ.filter (fun p => pairDistance X p = maximumDistance X)

def contactCount {n : ℕ} (X : Configuration n) : ℕ :=
  (contactPairs X).card

def diameterCount {n : ℕ} (X : Configuration n) : ℕ :=
  (diameterPairs X).card

def contactAdjacent {n : ℕ} (X : Configuration n) (i j : Fin n) : Prop :=
  i ≠ j ∧ pointDistance (X i) (X j) = minimumDistance X

def triangleFreeContact {n : ℕ} (X : Configuration n) : Prop :=
  ∀ i j k : Fin n, i ≠ j → j ≠ k → k ≠ i →
    ¬ (contactAdjacent X i j ∧ contactAdjacent X j k ∧ contactAdjacent X k i)

def contactFlex {n : ℕ} (X : Configuration n) (w : Configuration n) : Prop :=
  ∀ p ∈ contactPairs X,
    inner2 (X p.1.1 - X p.1.2) (w p.1.1 - w p.1.2) = 0

def rigidVelocity {n : ℕ} (X : Configuration n) (w : Configuration n) : Prop :=
  ∃ a : Point, ∃ ω : ℝ, ∀ i : Fin n,
    w i = a + ω • rotate90 (X i)

def diameterFunctional {n : ℕ} (X : Configuration n)
    (p : PairIndex n) (w : Configuration n) : ℝ :=
  2 * inner2 (X p.1.1 - X p.1.2) (w p.1.1 - w p.1.2) /
    (pairDistance X p) ^ 2

def firstOrderPositiveSpanning {n : ℕ} (X : Configuration n) : Prop :=
  ∀ w : Configuration n, contactFlex X w → ¬ rigidVelocity X w →
    (∃ p ∈ diameterPairs X, diameterFunctional X p w < 0) ∧
    (∃ p ∈ diameterPairs X, 0 < diameterFunctional X p w)

def firstOrderIsolatedLocalRatioMinimizer {n : ℕ}
    (X : Configuration n) : Prop :=
  normalized X ∧ localRatioMinimizer X ∧ firstOrderPositiveSpanning X

def hullVertex {n : ℕ} (X : Configuration n) (i : Fin n) : Prop :=
  X i ∈ Set.extremePoints ℝ (convexHull ℝ (Set.range X))

def hullCount {n : ℕ} (X : Configuration n) : ℕ :=
  (Finset.univ.filter (hullVertex X)).card

def closedSegment (a b : Point) : Set Point :=
  {z | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = a + t • (b - a)}

def openSegment (a b : Point) : Set Point :=
  {z | ∃ t : ℝ, 0 < t ∧ t < 1 ∧ z = a + t • (b - a)}

def disjointPairEndpoints {n : ℕ} (p q : PairIndex n) : Prop :=
  p.1.1 ≠ q.1.1 ∧ p.1.1 ≠ q.1.2 ∧
  p.1.2 ≠ q.1.1 ∧ p.1.2 ≠ q.1.2

def straightLinePlanar {n : ℕ} (X : Configuration n) : Prop :=
  ∀ p ∈ contactPairs X, ∀ q ∈ contactPairs X, p ≠ q →
    disjointPairEndpoints p q →
      ¬ ∃ z : Point,
        z ∈ openSegment (X p.1.1) (X p.1.2) ∧
          z ∈ openSegment (X q.1.1) (X q.1.2)

def straightLineDrawing {n : ℕ} (X : Configuration n) : Set Point :=
  {z | ∃ p ∈ contactPairs X,
    z ∈ closedSegment (X p.1.1) (X p.1.2)}

def faceRegionComponent {n : ℕ} (X : Configuration n)
    (U : Set Point) : Prop :=
  U.Nonempty ∧ IsConnected U ∧ IsOpen U ∧
    U ⊆ (straightLineDrawing X)ᶜ ∧
    ∀ V : Set Point, V.Nonempty → IsConnected V → IsOpen V →
      V ⊆ (straightLineDrawing X)ᶜ → U ⊆ V → V = U

def faceRegionPartition {n f : ℕ} (X : Configuration n)
    (regions : Fin f → Set Point) : Prop :=
  ∀ z : Point, z ∉ straightLineDrawing X →
    ∃! F : Fin f, z ∈ regions F

def dartTail {n : ℕ} (d : Dart n) : Fin n :=
  if d.2 then d.1.1.2 else d.1.1.1

def dartHead {n : ℕ} (d : Dart n) : Fin n :=
  if d.2 then d.1.1.1 else d.1.1.2

def dartReverse {n : ℕ} (d : Dart n) : Dart n :=
  (d.1, !d.2)

def cyclicNext {α : Type*} (l : List α) (a b : α) : Prop :=
  ∃ k : ℕ, ∃ t : List α, l.rotate k = a :: b :: t

def rotationValid {n : ℕ} (X : Configuration n)
    (rotation : Fin n → List (Dart n)) : Prop :=
  ∀ v : Fin n,
    (rotation v).Nodup ∧
      ∀ d : Dart n,
        d ∈ rotation v ↔ d.1 ∈ contactPairs X ∧ dartTail d = v

def faceSuccessor {n : ℕ}
    (rotation : Fin n → List (Dart n)) (d e : Dart n) : Prop :=
  dartHead d = dartTail e ∧
    cyclicNext (rotation (dartHead d)) (dartReverse d) e

def faceCycle {n : ℕ} (rotation : Fin n → List (Dart n))
    (cycle : List (Dart n)) : Prop :=
  cycle ≠ [] ∧ cycle.Nodup ∧
    (∀ d ∈ cycle, ∃ e ∈ cycle,
      cyclicNext cycle d e ∧ faceSuccessor rotation d e) ∧
    (∀ d e, cyclicNext cycle d e → faceSuccessor rotation d e)

def facePartition {n f : ℕ} (X : Configuration n)
    (faces : Fin f → List (List (Dart n))) : Prop :=
  ∀ d : Dart n, d.1 ∈ contactPairs X →
    ∃! F : Fin f, ∃ cycle ∈ faces F, d ∈ cycle

def faceBoundaryInRegion {n f : ℕ} (X : Configuration n)
    (faces : Fin f → List (List (Dart n)))
    (regions : Fin f → Set Point) : Prop :=
  ∀ F : Fin f, ∀ cycle ∈ faces F, ∀ d ∈ cycle,
    closedSegment (X (dartTail d)) (X (dartHead d)) ⊆ frontier (regions F)

def straightLinePlaneContactEmbedding {n f : ℕ}
    (X : Configuration n) (rotation : Fin n → List (Dart n))
    (faces : Fin f → List (List (Dart n)))
    (regions : Fin f → Set Point) (outer : Fin f) : Prop :=
  1 ≤ f ∧ rotationValid X rotation ∧ straightLinePlanar X ∧
    (faces outer).length > 0 ∧
    (∀ F : Fin f, (faces F).length > 0) ∧
    (∀ F : Fin f, ∀ cycle ∈ faces F, faceCycle rotation cycle) ∧
    facePartition X faces ∧ faceRegionPartition X regions ∧
    (∀ F : Fin f, faceRegionComponent X (regions F)) ∧
    (¬ IsBounded (regions outer)) ∧
    (∀ F : Fin f, F ≠ outer → IsBounded (regions F)) ∧
    faceBoundaryInRegion X faces regions

def faceDegree {n f : ℕ} (faces : Fin f → List (List (Dart n)))
    (F : Fin f) : ℕ :=
  ((faces F).map List.length).sum

def boundedFaceCount {f : ℕ} (outer : Fin f) : ℕ :=
  (Finset.univ.filter (fun F : Fin f => F ≠ outer)).card

def boundedFaceDegreeSum {n f : ℕ}
    (faces : Fin f → List (List (Dart n))) (outer : Fin f) : ℕ :=
  ∑ F : Fin f, if F ≠ outer then faceDegree faces F else 0

def faceExcess {n f : ℕ} (faces : Fin f → List (List (Dart n)))
    (outer : Fin f) : ℕ :=
  ∑ F : Fin f, if F ≠ outer then faceDegree faces F - 4 else 0

def isQuadrilateralFace {n f : ℕ}
    (faces : Fin f → List (List (Dart n))) (outer F : Fin f) : Prop :=
  F ≠ outer ∧ ∃ cycle : List (Dart n),
    faces F = [cycle] ∧ cycle.length = 4

def quadrilateralFaceCount {n f : ℕ}
    (faces : Fin f → List (List (Dart n))) (outer : Fin f) : ℕ :=
  (Finset.univ.filter (isQuadrilateralFace faces outer)).card

def nonQuadrilateralFaceCount {n f : ℕ}
    (faces : Fin f → List (List (Dart n))) (outer : Fin f) : ℕ :=
  (Finset.univ.filter (fun F => F ≠ outer ∧
    ¬ isQuadrilateralFace faces outer F)).card

def contactComponentReachable {n : ℕ} (X : Configuration n)
    (i j : Fin n) : Prop :=
  Relation.ReflTransGen (contactAdjacent X) i j

def contactComponentCount {n : ℕ} (X : Configuration n) : ℕ :=
  (Finset.univ.filter (fun i : Fin n =>
    ∀ j : Fin n, contactComponentReachable X j i → i ≤ j)).card

def hullBound (n : ℕ) : ℕ :=
  Nat.floor (Real.pi * Real.sqrt 2 *
    ((Nat.ceil (Real.sqrt (n : ℝ)) : ℝ) - 1))

/-- The oriented area used to state nondegeneracy of a planar
quadrilateral. -/
def cross (u v : Point) : ℝ :=
  u.1 * v.2 - u.2 * v.1

def interiorBoundarySegmentsMeet (a b c d : Point) : Prop :=
  ∃ z : Point,
    z ∈ openSegment a b ∧ z ∈ openSegment c d

def simpleNondegenerateQuadrilateral
    (a b c d : Point) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    cross (b - a) (c - b) ≠ 0 ∧
    cross (c - b) (d - c) ≠ 0 ∧
    cross (d - c) (a - d) ≠ 0 ∧
    cross (a - d) (b - a) ≠ 0 ∧
    ¬ interiorBoundarySegmentsMeet a b c d ∧
    ¬ interiorBoundarySegmentsMeet b c d a

def cycleVertices {n : ℕ} (cycle : List (Dart n)) : List (Fin n) :=
  cycle.map dartTail

def exactUnitRhombusCycle {n : ℕ} (X : Configuration n)
    (cycle : List (Dart n)) : Prop :=
  ∃ a b c d : Fin n,
    cycleVertices cycle = [a, b, c, d] ∧
    simpleNondegenerateQuadrilateral (X a) (X b) (X c) (X d) ∧
    pointDistance (X a) (X b) = 1 ∧
    pointDistance (X b) (X c) = 1 ∧
    pointDistance (X c) (X d) = 1 ∧
    pointDistance (X d) (X a) = 1 ∧
    X a + X c = X b + X d

/-- A degree-four bounded facial walk in the actual straight-line plane
contact embedding is an exact unit rhombus. -/
def claim33943_quadrilateral_faces_are_unit_rhombi : Prop :=
  ∀ (n f : ℕ) (X : Configuration n)
    (rotation : Fin n → List (Dart n))
    (faces : Fin f → List (List (Dart n)))
    (regions : Fin f → Set Point) (outer : Fin f),
    normalized X →
    straightLinePlaneContactEmbedding X rotation faces regions outer →
    ∀ F : Fin f, F ≠ outer →
      ∀ cycle : List (Dart n), cycle ∈ faces F → cycle.length = 4 →
        (cycleVertices cycle).Nodup ∧ exactUnitRhombusCycle X cycle

end
end MathlibPlus.Open.Geometry.PlanarUnitRhombus33943
