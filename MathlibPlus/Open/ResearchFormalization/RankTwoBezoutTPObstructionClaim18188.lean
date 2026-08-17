import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
open Set

namespace MathlibPlus.Open.ResearchFormalization.BatchR0135

noncomputable section

/-- The factorial-scaled weighted moment-curve cell. -/
def weightedMomentCurveCell (x w : Fin 3 → ℝ) : Matrix (Fin 3) ℕ ℝ :=
  fun n j =>
    w n * x n ^ j /
      (Nat.factorial (2 * j) : ℝ)

/-- Strict total positivity of a finite rectangular cell, over every finite
ordered choice of equally many rows and columns. -/
def finiteStrictTotalPositivity
    (B : Matrix (Fin 3) ℕ ℝ) : Prop :=
  ∀ (r : ℕ) (rows : Fin r ↪o Fin 3) (cols : Fin r → ℕ),
    StrictMono cols →
      0 < Matrix.det (fun i j => B (rows i) (cols j))

/-- The raw moment-curve sequence attached to the three nodes and weights. -/
def momentCurveValue
    (x w : Fin 3 → ℝ) (j : ℕ) : ℝ :=
  ∑ n : Fin 3, w n * x n ^ j

/-- Factorial-normalized coordinates `h_j=m_j/(2j)!`. -/
def rankTwoNormalizedMoment (m : Fin 4 → ℝ) (j : Fin 4) : ℝ :=
  m j / (Nat.factorial (2 * (j : ℕ)) : ℝ)

/-- The packet's rank-two Bezout matrix, formed from the four normalized
moment coordinates. -/
def rankTwoBezoutMatrix (m : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let h := rankTwoNormalizedMoment m
  !![h 0 * h 1, 2 * h 0 * h 2;
     2 * h 0 * h 2, 3 * h 0 * h 3 + h 1 * h 2]

/-- The two Lorentz slack coordinates. -/
def lorentzSlackZero (m : Fin 4 → ℝ) : ℝ :=
  m 0 * m 2 - (m 1) ^ 2

def lorentzSlackOne (m : Fin 4 → ℝ) : ℝ :=
  m 1 * m 3 - (m 2) ^ 2

/-- The exact conjunction of the positive-node/weight, moment-curve,
factorial-cell, strict-TP, and nonnegative-slack ingredients. -/
def rankTwoBezoutIngredients
    (x w : Fin 3 → ℝ) (m : Fin 4 → ℝ) : Prop :=
  (∀ n : Fin 3, 0 < x n ∧ 0 < w n) ∧
    StrictMono x ∧
    finiteStrictTotalPositivity (weightedMomentCurveCell x w) ∧
    (∀ j : Fin 4,
      m j = momentCurveValue x w (j : ℕ)) ∧
    0 ≤ lorentzSlackZero m ∧
    0 ≤ lorentzSlackOne m

/-- The universal implication that the listed ingredients would give rank-two
Bezout positivity. -/
def rankTwoBezoutPositivityImplication : Prop :=
  ∀ (x w : Fin 3 → ℝ) (m : Fin 4 → ℝ),
    rankTwoBezoutIngredients x w m →
      0 ≤ Matrix.det (rankTwoBezoutMatrix m)

/-- The concrete nodes and weights in the admitted three-atom collision. -/
def threeAtomNodes : Fin 3 → ℝ := ![1, 4, 100]

def threeAtomWeights : Fin 3 → ℝ := ![100, 1, 1]

def threeAtomMoments (j : ℕ) : ℝ :=
  momentCurveValue threeAtomNodes threeAtomWeights j

def threeAtomMomentVector : Fin 4 → ℝ :=
  fun j => threeAtomMoments (j : ℕ)

/-- The positive measure carried by the three displayed atoms. -/
def threeAtomMeasure : Measure ℝ :=
  (100 : ℝ≥0∞) • Measure.dirac (1 : ℝ) +
    Measure.dirac (4 : ℝ) + Measure.dirac (100 : ℝ)

def threeAtomMeasureMoment (j : ℕ) : ℝ :=
  ∫ x : ℝ, x ^ j ∂threeAtomMeasure

/-- The Lorentz-slack formulas and nonnegativity for the positive three-atom
measure, with the exact raw moment carrier retained. -/
def threeAtomLorentzSlackData : Prop :=
  threeAtomMeasure (Iio (0 : ℝ)) = 0 ∧
    (∀ j : ℕ,
      threeAtomMoments j = threeAtomMeasureMoment j) ∧
    lorentzSlackZero threeAtomMomentVector =
      (1 / 2 : ℝ) *
        (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2
          ∂(threeAtomMeasure.prod threeAtomMeasure)) ∧
    lorentzSlackOne threeAtomMomentVector =
      (1 / 2 : ℝ) *
        (∫ p : ℝ × ℝ, p.1 * p.2 * (p.1 - p.2) ^ 2
          ∂(threeAtomMeasure.prod threeAtomMeasure)) ∧
    0 ≤ lorentzSlackZero threeAtomMomentVector ∧
    0 ≤ lorentzSlackOne threeAtomMomentVector

/-- Claim 18188: the exact positive moment-curve/factorial-scaled strict-TP
three-atom data have nonnegative Lorentz slacks but a negative rank-two
Bezout determinant, so those ingredients alone do not imply positivity. -/
def strictTPAndPositiveLorentzSlacksDoNotImplyRankTwoBezoutPositivity_claim18188 : Prop :=
  ¬ rankTwoBezoutPositivityImplication ∧
    rankTwoBezoutIngredients
      threeAtomNodes threeAtomWeights threeAtomMomentVector ∧
    threeAtomLorentzSlackData ∧
    threeAtomMoments 0 = 102 ∧
    threeAtomMoments 1 = 204 ∧
    threeAtomMoments 2 = 10116 ∧
    threeAtomMoments 3 = 1000164 ∧
    rankTwoNormalizedMoment threeAtomMomentVector 0 = 102 ∧
    rankTwoNormalizedMoment threeAtomMomentVector 1 = 102 ∧
    rankTwoNormalizedMoment threeAtomMomentVector 2 = 843 / 2 ∧
    rankTwoNormalizedMoment threeAtomMomentVector 3 = 83347 / 60 ∧
    Matrix.det (rankTwoBezoutMatrix threeAtomMomentVector) =
      -(12619339326 : ℝ) / 5 ∧
    Matrix.det (rankTwoBezoutMatrix threeAtomMomentVector) < 0

end

end MathlibPlus.Open.ResearchFormalization.BatchR0135
