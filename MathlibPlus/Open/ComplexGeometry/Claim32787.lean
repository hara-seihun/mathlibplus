import Mathlib

namespace MathlibPlus.Open.ComplexGeometry.Claim32787

noncomputable section

abbrev RhombusPoint32787 := EuclideanSpace ℝ (Fin 2)

def rhombusU32787 : RhombusPoint32787 :=
  EuclideanSpace.single 0 1

def rhombusV32787 (a : ℝ) : RhombusPoint32787 :=
  a • EuclideanSpace.single 0 1 +
    Real.sqrt (1 - a ^ 2) • EuclideanSpace.single 1 1

def rhombusPoints32787 (a : ℝ) : Fin 4 → RhombusPoint32787 :=
  ![(0 : RhombusPoint32787), rhombusU32787, rhombusV32787 a,
    rhombusU32787 + rhombusV32787 a]

def rhombusSet32787 (a : ℝ) : Set RhombusPoint32787 :=
  Set.range (rhombusPoints32787 a)

def rhombusContact32787 (a : ℝ) (i j : Fin 4) : Prop :=
  dist (rhombusPoints32787 a i) (rhombusPoints32787 a j) = 1

def rhombusC4Adj32787 (i j : Fin 4) : Prop :=
  (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
  (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨
  (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) ∨
  (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)

def rhombusDistanceMatrix32787 (a : ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun i j => dist (rhombusPoints32787 a i) (rhombusPoints32787 a j)

def rhombusGram32787 (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![inner ℝ rhombusU32787 rhombusU32787,
      inner ℝ rhombusU32787 (rhombusV32787 a);
     inner ℝ (rhombusV32787 a) rhombusU32787,
      inner ℝ (rhombusV32787 a) (rhombusV32787 a)]

noncomputable def rhombusDiameter32787 (a : ℝ) : ℝ :=
  sSup (Set.range (fun ij : Fin 4 × Fin 4 =>
    rhombusDistanceMatrix32787 a ij.1 ij.2))

/-- The explicit continuous rhombic family has fixed binary contact graph but
varying physical nonedge distances and diameter. -/
def claim32787_binaryContactDoesNotDetermineEuclideanGramData : Prop :=
  Continuous (fun a : ℝ => rhombusPoints32787 a) ∧
    (∀ a : ℝ, 0 < a → a < 1 / 2 →
      rhombusSet32787 a =
        {0, rhombusU32787, rhombusV32787 a,
          rhombusU32787 + rhombusV32787 a} ∧
      ‖rhombusU32787‖ = 1 ∧
      ‖rhombusV32787 a‖ = 1 ∧
      inner ℝ rhombusU32787 (rhombusV32787 a) = a ∧
      (∀ i j : Fin 4,
        rhombusContact32787 a i j ↔ rhombusC4Adj32787 i j) ∧
      rhombusDistanceMatrix32787 a 1 2 ^ 2 = 2 - 2 * a ∧
      rhombusDistanceMatrix32787 a 0 3 ^ 2 = 2 + 2 * a ∧
      rhombusDiameter32787 a = Real.sqrt (2 + 2 * a)) ∧
    (∀ a b : ℝ,
      0 < a → a < 1 / 2 →
      0 < b → b < 1 / 2 →
      a < b →
      (∀ i j : Fin 4,
        rhombusContact32787 a i j ↔ rhombusContact32787 b i j) ∧
      rhombusDistanceMatrix32787 a ≠ rhombusDistanceMatrix32787 b ∧
      rhombusDistanceMatrix32787 a 1 2 ≠ rhombusDistanceMatrix32787 b 1 2 ∧
      rhombusDistanceMatrix32787 a 0 3 ≠ rhombusDistanceMatrix32787 b 0 3 ∧
      rhombusDiameter32787 a ≠ rhombusDiameter32787 b ∧
      rhombusGram32787 a ≠ rhombusGram32787 b)

end

end MathlibPlus.Open.ComplexGeometry.Claim32787
