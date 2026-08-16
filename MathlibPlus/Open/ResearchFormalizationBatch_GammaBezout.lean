import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch_GammaBezout

noncomputable section

/-- The rising factorial `(α)_n`. -/
def risingFactorial (α : ℝ) (n : ℕ) : ℝ :=
  ∏ u ∈ Finset.range n, (α + (u : ℝ))

/-- The completed even-jet cell from the admitted shifted-gamma realization. -/
def completedCell (α : ℝ) (p : ℕ) (v : ℝ) : ℝ :=
  (2 : ℝ) * Real.rpow v (2 * (p : ℝ) + 2 * α - 1) *
      Real.exp (-(v ^ 2)) / Real.Gamma α

def smoothPositiveCompletedCell (α : ℝ) (p : ℕ) : Prop :=
  ContDiffOn ℝ ⊤ (completedCell α p) (Set.Ioi 0) ∧
    ∀ v : ℝ, v ∈ Set.Ioi 0 → 0 < completedCell α p v

def completedJetMomentFromCell (α : ℝ) (p q : ℕ) : ℝ :=
  (1 / (Nat.factorial (2 * q) : ℝ)) *
    ∫ v in Set.Ioi (0 : ℝ), (v ^ (2 * q)) * completedCell α p v

def completedJetMoment (α : ℝ) (p q : ℕ) : ℝ :=
  risingFactorial α (p + q) / (Nat.factorial (2 * q) : ℝ)

def completedCellMomentFormula (α : ℝ) : Prop :=
  ∀ p q : ℕ,
    completedJetMomentFromCell α p q = completedJetMoment α p q

/-- Every increasing pair of nonnegative exponent lists has a strictly
positive completed moment minor. -/
def strictCompletedJetTotalPositivity (α : ℝ) : Prop :=
  ∀ (r : ℕ) (p q : Fin r → ℕ),
    StrictMono p → StrictMono q →
      0 < Matrix.det (fun i j : Fin r =>
        completedJetMoment α (p i) (q j))

/-- The shifted Kummer coefficient systems in the admitted recurrence. -/
def shiftedAcoef (α : ℝ) (j n : ℕ) : ℝ :=
  risingFactorial (α + (j : ℝ)) n /
    ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) *
      risingFactorial (2 * (j : ℝ) + (1 / 2 : ℝ)) n)

def shiftedPcoef (α : ℝ) (j n : ℕ) : ℝ :=
  risingFactorial (α + (j : ℝ) + 1) n /
    ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) *
      risingFactorial (2 * (j : ℝ) + (3 / 2 : ℝ)) n)

def shiftedKummerCoefficientSystems (α : ℝ) : Prop :=
  ∀ (j n : ℕ),
    ((n + 1 : ℕ) : ℝ) * shiftedAcoef α j (n + 1) =
      ((α + (j : ℝ)) / (2 * (4 * (j : ℝ) + 1))) *
        shiftedPcoef α j n

/-- The explicit positive denominator sequence in the pivot formula. -/
def gammaQ (j : ℕ) : ℝ :=
  2 * ∏ u ∈ Finset.range j,
    (2 * (4 * (u : ℝ) + 1) *
      (4 * (u : ℝ) + 3) ^ 2 * (4 * (u : ℝ) + 5))

def gammaPivot (α : ℝ) (j : ℕ) : ℝ :=
  (∏ u ∈ Finset.range (j + 1), (α + (u : ℝ))) *
      (∏ u ∈ Finset.range j, (2 * α - (2 * (u : ℝ) + 1))) /
    gammaQ j

def completedBezoutH (α : ℝ) (j : ℕ) : ℝ :=
  risingFactorial α j / (Nat.factorial (2 * j) : ℝ)

/-- The exact finite completed quadratic Bezout section. -/
def completedBezoutSection (α : ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    ∑ a ∈ Finset.range (Nat.min i.val j.val + 1),
      ((i.val + j.val + 1 - 2 * a : ℕ) : ℝ) *
        completedBezoutH α a *
        completedBezoutH α (i.val + j.val + 1 - a)

def gammaL (α : ℝ) (i j : ℕ) : ℝ :=
  if j > i then 0 else
    risingFactorial (α + (j : ℝ) + 1) (i - j) /
      ((4 : ℝ) ^ (i - j) * (Nat.factorial (i - j) : ℝ) *
        risingFactorial (2 * (j : ℝ) + (3 / 2 : ℝ)) (i - j))

def gammaLDLFactorization (α : ℝ) (N : ℕ) : Prop :=
  let L : Matrix (Fin N) (Fin N) ℝ := fun i j => gammaL α i.val j.val
  let D : Matrix (Fin N) (Fin N) ℝ := fun i j =>
    if i = j then gammaPivot α i.val else 0
  completedBezoutSection α N = (L * D) * L.transpose

def positiveHalfInteger (α : ℝ) : Prop :=
  ∃ r : ℕ, 1 ≤ r ∧ α = (r : ℝ) - (1 / 2 : ℝ)

def abstractCompletedCellHypotheses (α : ℝ) : Prop :=
  (∀ p : ℕ, smoothPositiveCompletedCell α p) ∧
    completedCellMomentFormula α ∧
    strictCompletedJetTotalPositivity α ∧
    shiftedKummerCoefficientSystems α ∧
    (∀ N : ℕ, gammaLDLFactorization α N)

def strictCompletedBezoutPositivity (α : ℝ) : Prop :=
  ∀ j : ℕ, 0 < gammaPivot α j

/-- Claim 10527: the concrete shifted-gamma cells satisfy the stated
all-rank hypotheses while a finite completed-Bezout pivot is nonpositive,
and every non-half-integer shape has a negative pivot. -/
def claim10527_completedCellTPDoesNotForceBezoutPositivity : Prop :=
  (∀ α : ℝ, 0 < α →
    abstractCompletedCellHypotheses α ∧
      (∃ N j : ℕ, 0 < N ∧ j < N ∧ gammaPivot α j ≤ 0)) ∧
    (∀ α : ℝ, 0 < α → ¬ positiveHalfInteger α →
      ∃ j : ℕ, gammaPivot α j < 0) ∧
    ¬ (∀ α : ℝ,
      0 < α → abstractCompletedCellHypotheses α →
        strictCompletedBezoutPositivity α)

end

end MathlibPlus.Open.ResearchFormalizationBatch_GammaBezout
