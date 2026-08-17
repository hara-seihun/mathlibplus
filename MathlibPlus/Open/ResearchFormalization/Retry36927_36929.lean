import Mathlib
import MathlibPlus.Open.Research.FormalizationBatch_01a004d6

open scoped BigOperators
open MathlibPlus.Open.Research.FormalizationBatch

namespace MathlibPlus.Open.ResearchFormalizationBatch.Retry36927

private abbrev Cube5 := Fin 5 → Bool
private abbrev DirectionDomain5 (i : Fin 5) := DirectionDomain 5 i
private abbrev Staircase5 :=
  (i : Fin 5) → DirectionDomain5 i → Bool

private def q5Full (i : Fin 5) (x : Cube5) : Bool :=
  if i = 0 then x 1 && (x 2 || x 3)
  else if i = 1 then x 2 || x 3
  else if i = 2 then (!x 1) && x 3
  else if i = 3 then (!x 1) || (!x 2)
  else (!x 3) && ((!x 1) || (!x 2))

private def q5Witness : Staircase5 :=
  fun i x => q5Full i x.1

private def staircaseSystem {n : ℕ}
    (f : (i : Fin n) → DirectionDomain n i → Bool) : Prop :=
  ∀ (i j : Fin n), i ≠ j →
    ((j.val < i.val →
        coordinateDecreasing (directionValue f i) j) ∧
      (i.val < j.val →
        coordinateIncreasing (directionValue f i) j))

private def q5StaircaseMonotonicity : Prop :=
  staircaseSystem q5Witness

private def q5MinimumSliceProducts : Prop :=
  ∀ x : Cube5,
    (false = false) ∧
    (x 1 && x 3 && ((!x 1) && x 3) = false) ∧
    (x 1 && x 2 && ((!x 1) || (!x 2)) = false) ∧
    (x 1 && (x 2 || x 3) &&
      ((!x 3) && ((!x 1) || (!x 2))) = false) ∧
    (x 3 && false = false) ∧
    (x 2 && (!x 2) = false) ∧
    ((x 2 || x 3) && ((!x 3) && (!x 2)) = false) ∧
    (false = false) ∧
    (((!x 1) && x 3) && ((!x 3) && (!x 1)) = false) ∧
    (false = false)

private def q5OwnCoordinateIndependence : Prop :=
  ∀ (i : Fin 5) (x : Cube5),
    q5Full i (Function.update x i false) =
      q5Full i (Function.update x i true)

private def q5AllCoordinateSquares : Prop :=
  ∀ (i j : Fin 5) (x : Cube5),
    i.val < j.val → ¬ coordinateSquare q5Witness i j x

private def q5DirectionCounts : Prop :=
  directionCount q5Witness 0 = 6 ∧
  directionCount q5Witness 1 = 12 ∧
  directionCount q5Witness 2 = 4 ∧
  directionCount q5Witness 3 = 12 ∧
  directionCount q5Witness 4 = 6 ∧
  selectedEdgeCount q5Witness = 40 ∧
  (selectedEdgeCount q5Witness : ℚ) / 16 = 5 / 2 ∧
  (∀ i : Fin 5, directionCount q5Witness i < 16)

private def q5FullPivot : Prop :=
  ∃ i : Fin 5, directionCount q5Witness i = 16

/-- The staircase square criterion together with the complete finite Q5 check. -/
def claim36927 : Prop :=
  (∀ {n : ℕ}
      (f : (i : Fin n) → DirectionDomain n i → Bool),
      staircaseSystem f →
      ∀ (i j : Fin n) (x : Cube n),
        i.val < j.val → x i = false → x j = false →
        (coordinateSquare f i j x ↔
          directionValue f i x = true ∧
          directionValue f j (Function.update x i true) = true)) ∧
  q5OwnCoordinateIndependence ∧
  q5StaircaseMonotonicity ∧
  q5MinimumSliceProducts ∧
  q5AllCoordinateSquares ∧
  q5DirectionCounts

/-- The Q5 witness refutes the full-pivot induction premise without asserting
or refuting the all-order recurrence. -/
def claim36929 : Prop :=
  q5StaircaseMonotonicity ∧
  isC4Free (cubeAdjacency q5Witness) ∧
  q5DirectionCounts ∧
  ¬ q5FullPivot ∧
  ¬ (∀ (f : Staircase5),
      staircaseSystem f →
      isC4Free (cubeAdjacency f) →
      (selectedEdgeCount f : ℚ) / 16 = 5 / 2 →
      ∃ i : Fin 5, directionCount f i = 16)

end MathlibPlus.Open.ResearchFormalizationBatch.Retry36927
