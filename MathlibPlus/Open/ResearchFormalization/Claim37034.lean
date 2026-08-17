import Mathlib

open Filter Topology

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

abbrev PlanarPoint := ℝ × ℝ

/-- Euclidean norm and distance on the planar carrier used by the nested-shell
construction. -/
def euclideanNorm (p : PlanarPoint) : ℝ :=
  Real.sqrt (p.1 ^ 2 + p.2 ^ 2)

def euclideanDistance (p q : PlanarPoint) : ℝ :=
  euclideanNorm (p - q)

/-- The radius, inradius, and diameter of the side-one regular `q`-gon. -/
def polygonRadius (q : ℕ) : ℝ :=
  1 / (2 * Real.sin (Real.pi / (q : ℝ)))

def polygonInradius (q : ℕ) : ℝ :=
  polygonRadius q * Real.cos (Real.pi / (q : ℝ))

def polygonDiameter (q : ℕ) : ℝ :=
  1 / (2 * Real.sin (Real.pi / (2 * (q : ℝ))))

def polygonPoint (q : ℕ) (i : Fin q) : PlanarPoint :=
  let θ : ℝ := 2 * Real.pi * (i.val : ℝ) / (q : ℝ)
  (polygonRadius q * Real.cos θ, polygonRadius q * Real.sin θ)

/-- The vertices of the regular side-one polygon. -/
noncomputable def regularPolygon (q : ℕ) : Finset PlanarPoint := by
  classical
  exact (Finset.univ : Finset (Fin q)).image (polygonPoint q)

def polygonVertices (q : ℕ) : Set PlanarPoint :=
  (regularPolygon q : Set PlanarPoint)

def polygonRegion (q : ℕ) : Set PlanarPoint :=
  convexHull ℝ (polygonVertices q)

/-- An explicit unit-basis realization of the sheared triangular lattice in the
source construction. -/
def latticeShear (M : ℕ) : ℝ :=
  1 / 2 - 1 / (M : ℝ) ^ 2

def latticeU (_M : ℕ) : PlanarPoint :=
  (1, 0)

def latticeV (M : ℕ) : PlanarPoint :=
  (latticeShear M, Real.sqrt (1 - latticeShear M ^ 2))

def latticePoint (M : ℕ) (a b : ℤ) : PlanarPoint :=
  (a : ℝ) • latticeU M + (b : ℝ) • latticeV M

def latticeSet (M : ℕ) : Set PlanarPoint :=
  Set.range (fun ab : ℤ × ℤ => latticePoint M ab.1 ab.2)

def euclideanBall (R : ℝ) : Set PlanarPoint :=
  {p | euclideanNorm p ≤ R}

def latticeBulk (M : ℕ) : Set PlanarPoint :=
  latticeSet M ∩ euclideanBall (polygonRadius M - 2)

/-- The fixed nested-shell family, with `M=m-8`. -/
def nestedShell (m : ℕ) : Set PlanarPoint :=
  polygonVertices m ∪ polygonVertices (m - 8) ∪ latticeBulk (m - 8)

def retainedCore (m : ℕ) : Set PlanarPoint :=
  polygonVertices (m - 8) ∪ latticeBulk (m - 8)

def pointCount (X : Set PlanarPoint) : ℕ :=
  X.ncard

def distanceSpectrum (X : Set PlanarPoint) : Set ℝ :=
  {d | ∃ p ∈ X, ∃ q ∈ X, d = euclideanDistance p q}

def nonzeroDistanceSpectrum (X : Set PlanarPoint) : Set ℝ :=
  {d | ∃ p ∈ X, ∃ q ∈ X, p ≠ q ∧ d = euclideanDistance p q}

def diameter (X : Set PlanarPoint) : ℝ :=
  sSup (distanceSpectrum X)

def minimumDistance (X : Set PlanarPoint) : ℝ :=
  sInf (nonzeroDistanceSpectrum X)

def diameterRatio (X : Set PlanarPoint) : ℝ :=
  diameter X / minimumDistance X

/-- The unit-separated and triangle-free predicates on a point set. -/
def unitSeparated (X : Set PlanarPoint) : Prop :=
  ∀ ⦃p q : PlanarPoint⦄, p ∈ X → q ∈ X → p ≠ q →
    1 ≤ euclideanDistance p q

def hasUnitTriangle (X : Set PlanarPoint) : Prop :=
  ∃ a b c : PlanarPoint,
    a ∈ X ∧ b ∈ X ∧ c ∈ X ∧
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    euclideanDistance a b = 1 ∧
    euclideanDistance b c = 1 ∧
    euclideanDistance c a = 1

def triangleFree (X : Set PlanarPoint) : Prop :=
  ¬ hasUnitTriangle X

/-- The exact first-peel carrier and its two displayed diameter values. -/
def firstPeelExact (m : ℕ) : Prop :=
  nestedShell m \ polygonVertices m = retainedCore m ∧
    diameter (retainedCore m) = polygonDiameter (m - 8) ∧
    diameter (nestedShell m) = polygonDiameter m

def firstPeelLoss (m : ℕ) : ℝ :=
  diameter (nestedShell m) - diameter (retainedCore m)

/-- Minkowski addition and the filled-polygon moat width. -/
def minkowskiSum (A B : Set PlanarPoint) : Set PlanarPoint :=
  {p | ∃ a ∈ A, ∃ b ∈ B, p = a + b}

def moatWidth (m : ℕ) : ℝ :=
  sSup {w : ℝ |
    0 ≤ w ∧
      minkowskiSum (polygonRegion (m - 8)) (euclideanBall w) ⊆
        polygonRegion m}

/-- The natural labelled local-minimum predicate for diameter divided by
minimum distance. -/
def labelledLocalRatioMinimum {n : ℕ} (x : Fin n → PlanarPoint) : Prop :=
  Function.Injective x ∧
    ∃ δ : ℝ, 0 < δ ∧
      ∀ y : Fin n → PlanarPoint,
        (∀ i : Fin n, euclideanDistance (x i) (y i) < δ) →
          diameterRatio (Set.range x) ≤ diameterRatio (Set.range y)

def localRatioMinimum (X : Set PlanarPoint) : Prop :=
  ∃ n : ℕ, ∃ x : Fin n → PlanarPoint,
    Set.range x = X ∧ labelledLocalRatioMinimum x

/-- Cyclic indices on an odd polygon. -/
def shiftedIndex (m : ℕ) (hm : 0 < m) (i : Fin m) (d : ℕ) : Fin m :=
  ⟨(i.val + d) % m, Nat.mod_lt _ hm⟩

def sideForce (m : ℕ) (hm : 0 < m) (i : Fin m) : PlanarPoint :=
  (polygonPoint m (shiftedIndex m hm i 1) - polygonPoint m i) +
    (polygonPoint m (shiftedIndex m hm i (m - 1)) - polygonPoint m i)

def farthestForce (m : ℕ) (hm : 0 < m) (i : Fin m) : PlanarPoint :=
  let h := (m - 1) / 2
  (polygonPoint m (shiftedIndex m hm i h) - polygonPoint m i) +
    (polygonPoint m (shiftedIndex m hm i (m - h)) - polygonPoint m i)

/-- The uniform contact-minus-diameter KKT equilibrium on the outer odd
polygon.  The two cycle weights are fixed at `1/m`, with the diameter
normalization appearing in the signed stress. -/
def balancedOuterShellKKT (m : ℕ) : Prop :=
  Odd m ∧ 7 ≤ m ∧
    ∀ (hm : 0 < m) (i : Fin m),
      ((1 / (m : ℝ)) : ℝ) • sideForce m hm i -
          ((1 / (m : ℝ)) / polygonDiameter m ^ 2) • farthestForce m hm i =
        (0, 0)

/-- A finite Delaunay face is a three-point subset with an empty circumdisk. -/
def isDelaunayFace (X : Set PlanarPoint) (F : Finset PlanarPoint) : Prop :=
  F.card = 3 ∧
    (↑F : Set PlanarPoint) ⊆ X ∧
    ∃ center : PlanarPoint, ∃ radius : ℝ,
      0 ≤ radius ∧
        (∀ p ∈ F, euclideanDistance p center = radius) ∧
        (∀ p ∈ X, p ∉ (F : Set PlanarPoint) →
          radius ≤ euclideanDistance p center)

def shortDiagonal (M : ℕ) : ℝ :=
  Real.sqrt (1 + 2 / (M : ℝ) ^ 2)

def nearEquilateralFace (M : ℕ) (F : Finset PlanarPoint) : Prop :=
  ∃ p q r : PlanarPoint,
    F = {p, q, r} ∧
    p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
    euclideanDistance p q = 1 ∧
    euclideanDistance q r = 1 ∧
    euclideanDistance r p = shortDiagonal M

def nearEquilateralDelaunayFaces
    (X : Set PlanarPoint) (M : ℕ) : Set (Finset PlanarPoint) :=
  {F | isDelaunayFace X F ∧ nearEquilateralFace M F}

def nearFaceCount (X : Set PlanarPoint) (M : ℕ) : ℕ :=
  (nearEquilateralDelaunayFaces X M).ncard

def nearFaceDeficit (X : Set PlanarPoint) (M : ℕ) : ℝ :=
  2 * (pointCount X : ℝ) - nearFaceCount X M

noncomputable def totalShortDiagonalSlack (X : Set PlanarPoint) (M : ℕ) : ℝ := by
  classical
  exact ∑' F : Finset PlanarPoint,
    if F ∈ nearEquilateralDelaunayFaces X M then
      shortDiagonal M - 1
    else 0

/-- The asymptotic Delaunay statement in the source's `2|X|-O(sqrt |X|)`
and `O(1)` form. -/
def oneWellDelaunayNearCrystallization : Prop :=
  ∃ A B : ℝ,
    0 ≤ A ∧ 0 ≤ B ∧
      (∀ᶠ k : ℕ in atTop,
        nearFaceDeficit (nestedShell (2 * k + 19)) (2 * k + 11) ≤
          A * Real.sqrt (pointCount (nestedShell (2 * k + 19)) : ℝ)) ∧
      (∀ᶠ k : ℕ in atTop,
        totalShortDiagonalSlack
            (nestedShell (2 * k + 19)) (2 * k + 11) ≤ B)

/-- The odd large-index subsequence used by the construction. -/
def oddShellIndex (k : ℕ) : ℕ :=
  2 * k + 19

def optimalLeadingPackingScale : Prop :=
  Tendsto
    (fun k : ℕ =>
      diameter (nestedShell (oddShellIndex k)) /
        Real.sqrt (pointCount (nestedShell (oddShellIndex k)) : ℝ))
    atTop (𝓝 (Real.sqrt (2 * Real.sqrt 3 / Real.pi)))

/-- Claim 37034.  The exact first-peel and first-moat limits leave both
sharpened one-layer budgets valid, while the same explicit family has the
local-ratio, KKT, leading-scale, and one-well Delaunay properties and remains
triangle-free.  No global-minimizer predicate is included: the source makes
no global-optimality claim. -/
def claim37034 : Prop :=
  8 / Real.pi < 3 * Real.sqrt 3 / 2 ∧
    4 / Real.pi < 3 * Real.sqrt 3 / 4 ∧
    Tendsto
      (fun k : ℕ => firstPeelLoss (oddShellIndex k))
      atTop (𝓝 (8 / Real.pi)) ∧
    Tendsto
      (fun k : ℕ => moatWidth (oddShellIndex k))
      atTop (𝓝 (4 / Real.pi)) ∧
    (∀ᶠ k : ℕ in atTop,
      let X := nestedShell (oddShellIndex k)
      X.Finite ∧
        unitSeparated X ∧
        triangleFree X ∧
        firstPeelExact (oddShellIndex k) ∧
        firstPeelLoss (oddShellIndex k) < 3 * Real.sqrt 3 / 2 ∧
        moatWidth (oddShellIndex k) < 3 * Real.sqrt 3 / 4 ∧
        localRatioMinimum X ∧
        balancedOuterShellKKT (oddShellIndex k)) ∧
    optimalLeadingPackingScale ∧
    oneWellDelaunayNearCrystallization

end

end MathlibPlus.Open.ResearchFormalization
