import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R3267UnitLattice

noncomputable section

abbrev Point := EuclideanSpace ℝ (Fin 2)

def latticeC (r : ℤ) : ℝ :=
  (1 / 2 : ℝ) - ((r : ℝ)⁻¹) ^ 4

def latticeS (r : ℤ) : ℝ :=
  Real.sqrt (1 - latticeC r ^ 2)

def latticeU : Point :=
  (WithLp.equiv (2 : ENNReal) (Fin 2 → ℝ)).symm ![(1 : ℝ), (0 : ℝ)]

def latticeV (r : ℤ) : Point :=
  (WithLp.equiv (2 : ENNReal) (Fin 2 → ℝ)).symm
    ![latticeC r, latticeS r]

def latticePoint (r : ℤ) (a b : ℤ) : Point :=
  (a : ℝ) • latticeU + (b : ℝ) • latticeV r

def lattice (r : ℤ) : Set Point :=
  Set.range (fun p : ℤ × ℤ => latticePoint r p.1 p.2)

def latticeDisk (r : ℤ) : Set Point :=
  Metric.closedBall (0 : Point) (r : ℝ)

def truncatedLattice (r : ℤ) : Set Point :=
  lattice r ∩ latticeDisk r

def latticeCardinality (r : ℤ) : ℕ :=
  Set.ncard (truncatedLattice r)

def latticeSquaredNorm (r : ℤ) (a b : ℤ) : ℝ :=
  ‖latticePoint r a b‖ ^ 2

def latticeQuadratic (r : ℤ) (a b : ℤ) : ℝ :=
  (a : ℝ) ^ 2 + (b : ℝ) ^ 2 +
    2 * latticeC r * (a : ℝ) * (b : ℝ)

def squareCoordinateEdge (a b a' b' : ℤ) : Prop :=
  (a - a' = 1 ∧ b = b') ∨
    (a - a' = -1 ∧ b = b') ∨
    (a = a' ∧ b - b' = 1) ∨
    (a = a' ∧ b - b' = -1)

def fullLatticeUnitEdge (r : ℤ) (a b a' b' : ℤ) : Prop :=
  dist (latticePoint r a b) (latticePoint r a' b') = 1

def latticeUnitSeparated (r : ℤ) : Prop :=
  ∀ ⦃x y : Point⦄, x ∈ truncatedLattice r → y ∈ truncatedLattice r →
    x ≠ y → 1 ≤ dist x y

def squareColor (a b : ℤ) : Bool :=
  decide (Even (a + b))

def unitDistanceEdge (X : Set Point) (x y : Point) : Prop :=
  x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ dist x y = 1

def squareLatticeEdge (r : ℤ) (x y : Point) : Prop :=
  ∃ a b a' b' : ℤ,
    x = latticePoint r a b ∧ y = latticePoint r a' b' ∧
      squareCoordinateEdge a b a' b' ∧
      squareColor a b ≠ squareColor a' b'

def triangleFreeUnitDistanceGraph (X : Set Point) : Prop :=
  ∀ x y z : Point,
    x ∈ X → y ∈ X → z ∈ X → x ≠ y → y ≠ z → x ≠ z →
      ¬ (dist x y = 1 ∧ dist y z = 1 ∧ dist z x = 1)

def claim_46354 : Prop :=
  ∀ r : ℤ, 4 ≤ r →
    (∀ a b : ℤ,
      latticeSquaredNorm r a b = latticeQuadratic r a b) ∧
    (∀ a b : ℤ, (a, b) ≠ (0, 0) →
      latticeQuadratic r a b ≥ 1 ∧
        (latticeQuadratic r a b = 1 ↔
          ((a = 1 ∧ b = 0) ∨
            (a = -1 ∧ b = 0) ∨
            (a = 0 ∧ b = 1) ∨
            (a = 0 ∧ b = -1)))) ∧
    latticeUnitSeparated r ∧
    (∀ a b a' b' : ℤ,
      fullLatticeUnitEdge r a b a' b' ↔
        squareCoordinateEdge a b a' b')

def claim_46359 : Prop :=
  ∀ r : ℤ, 4 ≤ r →
    (∀ x y : Point,
      unitDistanceEdge (lattice r) x y → squareLatticeEdge r x y) ∧
    (∀ x y : Point,
      unitDistanceEdge (truncatedLattice r) x y → squareLatticeEdge r x y) ∧
    triangleFreeUnitDistanceGraph (lattice r) ∧
    triangleFreeUnitDistanceGraph (truncatedLattice r)

def fundamentalParallelogram (r : ℤ) : Set Point :=
  {z | ∃ a b : ℝ,
    |a| ≤ (1 / 2 : ℝ) ∧ |b| ≤ (1 / 2 : ℝ) ∧
      z = a • latticeU + b • latticeV r}

def claim_46362 : Prop :=
  ∀ r : ℤ, 4 ≤ r →
    Real.pi * ((r : ℝ) - 1) ^ 2 / latticeS r ≤
        (latticeCardinality r : ℝ) ∧
      (latticeCardinality r : ℝ) ≤
        Real.pi * ((r : ℝ) + 1) ^ 2 / latticeS r ∧
      MeasureTheory.volume (fundamentalParallelogram r) =
        ENNReal.ofReal (latticeS r) ∧
      ∀ z ∈ fundamentalParallelogram r, ‖z‖ ≤ 1

def interiorLattice (r : ℤ) : Set Point :=
  lattice r ∩ Metric.ball (0 : Point) ((r : ℝ) - 2)

def relativeVoronoiCell (r : ℤ) (x : Point) : Set Point :=
  {z | ∀ y : Point, y ∈ truncatedLattice r → dist z x ≤ dist z y}

def pointDot (x y : Point) : ℝ :=
  ∑ i, x i * y i

def alphaCoordinate (z : Point) : ℝ :=
  pointDot z latticeU

def betaCoordinate (r : ℤ) (z : Point) : ℝ :=
  pointDot z (latticeV r)

def fullLatticeVoronoiPolygon (r : ℤ) : Set Point :=
  {z |
    |alphaCoordinate z| ≤ (1 / 2 : ℝ) ∧
      |betaCoordinate r z| ≤ (1 / 2 : ℝ) ∧
      |alphaCoordinate z - betaCoordinate r z| ≤ 1 - latticeC r}

def pointTranslate (x : Point) (P : Set Point) : Set Point :=
  {z | ∃ p : Point, p ∈ P ∧ z = x + p}

def interiorNeighborsInDisk (r : ℤ) (x : Point) : Prop :=
  x + latticeU ∈ latticeDisk r ∧
    x - latticeU ∈ latticeDisk r ∧
    x + latticeV r ∈ latticeDisk r ∧
    x - latticeV r ∈ latticeDisk r ∧
    x + (latticeU - latticeV r) ∈ latticeDisk r ∧
    x - (latticeU - latticeV r) ∈ latticeDisk r

def claim_46378 : Prop :=
  ∀ r : ℤ, 4 ≤ r →
    ∀ x : Point, x ∈ interiorLattice r →
      interiorNeighborsInDisk r x ∧
        relativeVoronoiCell r x =
          pointTranslate x (fullLatticeVoronoiPolygon r) ∧
        MeasureTheory.volume (relativeVoronoiCell r x) =
          ENNReal.ofReal (latticeS r)

end

end MathlibPlus.Open.ResearchFormalization.R3267UnitLattice
