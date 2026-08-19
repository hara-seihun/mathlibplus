import Mathlib

namespace MathlibPlus.Open.LinearAlgebra.Claim59118

noncomputable section
open Classical

/-- The one base column has incidence coefficient `A = 1` and target `b = 0`. -/
def oneColumnIncidence59118 (x : ℝ) : ℝ := x

def oneColumnTarget59118 : ℝ := 0

/-- The feasible opposite-orientation pair at parameter `t`. -/
def oneColumnOppositePair59118 (t : ℝ) : ℝ × ℝ := (t, t)

def oneColumnFeasible59118 (t : ℝ) : Prop :=
  0 ≤ (oneColumnOppositePair59118 t).1 ∧
    0 ≤ (oneColumnOppositePair59118 t).2 ∧
    oneColumnIncidence59118
        ((oneColumnOppositePair59118 t).1 -
          (oneColumnOppositePair59118 t).2) = oneColumnTarget59118

/-- Response of the two typed copy columns on an opposite pair. -/
def copyResponse59118 (qPlus qMinus xPlus xMinus : ℝ) : ℝ :=
  qPlus * xPlus + qMinus * xMinus

/-- The image of all feasible opposite pairs for fixed typed copy columns. -/
def copyImage59118 (qPlus qMinus : ℝ) : Set ℝ :=
  {y | ∃ t : ℝ, 0 ≤ t ∧
    y = copyResponse59118 qPlus qMinus
      (oneColumnOppositePair59118 t).1
      (oneColumnOppositePair59118 t).2}

/-- A scalar nonnegative ray, including the zero-generator case. -/
def nonnegativeRay59118 (v : ℝ) : Set ℝ :=
  {y | ∃ t : ℝ, 0 ≤ t ∧ y = v * t}

/-- The even part of the two typed response columns. -/
def evenPart59118 (qPlus qMinus : ℝ) : ℝ :=
  (qPlus + qMinus) / 2

/-- Swapping the two orientation coordinates. -/
def swapPair59118 (x : ℝ × ℝ) : ℝ × ℝ := (x.2, x.1)

/-- Oddness of the typed response map under orientation reversal. -/
def responseOdd59118 (qPlus qMinus : ℝ) : Prop :=
  ∀ x : ℝ × ℝ,
    copyResponse59118 qPlus qMinus
        (swapPair59118 x).1 (swapPair59118 x).2 =
      -copyResponse59118 qPlus qMinus x.1 x.2

/-- Equal scalar columns need not give an odd typed copy map. -/
def equalCopyIsNotOdd59118 : Prop :=
  ¬ responseOdd59118 1 1

/-- Claim 59118: the feasible opposite pair is the nonnegative one-column
ray; equal copies retain that ray, opposite copies cancel it, and arbitrary
copies retain precisely their even component. -/
def claim59118_evenCopyParityRecessionRay : Prop :=
  (∀ t : ℝ, 0 ≤ t → oneColumnFeasible59118 t) ∧
    (copyImage59118 1 1 = Set.Ici (0 : ℝ)) ∧
    (copyImage59118 1 (-1) = ({0} : Set ℝ)) ∧
    (∀ qPlus qMinus : ℝ,
      copyImage59118 qPlus qMinus =
        nonnegativeRay59118 (2 * evenPart59118 qPlus qMinus)) ∧
    equalCopyIsNotOdd59118

end

end MathlibPlus.Open.LinearAlgebra.Claim59118
