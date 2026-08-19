import Mathlib
import MathlibPlus.Analysis.CheckerboardBezout

namespace MathlibPlus.Open.ResearchFormalization.O0153.Claim13640

open Filter Asymptotics MeasureTheory Set Topology
open scoped BigOperators

noncomputable section

/-- The completed theta shell appearing in the primitive moments. -/
def thetaShell (u : ℝ) : ℝ :=
  ∑' m : ℕ,
    if 1 ≤ m then
      Real.exp (-Real.pi * (m : ℝ) ^ 2 * Real.exp (2 * u))
    else 0

/-- The primitive moment sequence used by the checkerboard columns. -/
def thetaMoment (n : ℕ) : ℝ :=
  2 * (∫ u in Ioi (0 : ℝ),
    Real.exp (u / 2) * thetaShell u * u ^ (2 * n)) /
    (Nat.factorial (2 * n) : ℝ)

/-- The finite positive-side Bezout matrix from the checkerboard transfer. -/
def positiveBezout (n c : ℕ) : ℝ :=
  MathlibPlus.Analysis.CheckerboardBezout.checkerboardBezoutEntry
    thetaMoment n c

/-- The lower-shift realization of `(α I - Z) B⁺ (α I - Z)ᵀ`. -/
def checkerboardTransfer (α : ℝ) (n c : ℕ) : ℝ :=
  α ^ 2 * positiveBezout n c
    - α * (if 0 < n then positiveBezout (n - 1) c else 0)
    - α * (if 0 < c then positiveBezout n (c - 1) else 0)
    + (if 0 < n ∧ 0 < c then positiveBezout (n - 1) (c - 1) else 0)

/-- The exact first checkerboard column. -/
def firstColumn (α b : ℝ) (n : ℕ) : ℝ :=
  (b * ((n + 1 : ℕ) : ℝ) - α * (n : ℝ) * thetaMoment 0) *
      thetaMoment n -
    α * ((n + 1 : ℕ) : ℝ) * (b - α * thetaMoment 0) *
      thetaMoment (n + 1)

/-- The exact second fixed-column carrier, obtained from the same
checkerboard transfer rather than from an independent sequence. -/
def secondColumn (α : ℝ) (n : ℕ) : ℝ :=
  checkerboardTransfer α n 1

def normalizedSecondColumn (α b : ℝ) (n : ℕ) : ℝ :=
  secondColumn α n / firstColumn α b n

def firstBoundaryMultiplier (α b : ℝ) (n : ℕ) : ℝ :=
  firstColumn α b n / firstColumn α b (n - 1)

def twoFlagMinor (α b : ℝ) (n : ℕ) : ℝ :=
  firstColumn α b (n - 1) * secondColumn α n -
    secondColumn α (n - 1) * firstColumn α b n

def secondBoundaryMultiplier (α b : ℝ) (n : ℕ) : ℝ :=
  twoFlagMinor α b n * firstColumn α b (n - 2) /
    (twoFlagMinor α b (n - 1) * firstColumn α b (n - 1))

/-- The positive principal branch used in the boundary scale. -/
def principalLambertW (x : ℝ) : ℝ :=
  sInf {y : ℝ | 0 ≤ y ∧ y * Real.exp y = x}

def lambertBoundaryScale (n : ℕ) : ℝ :=
  principalLambertW (2 * (n : ℝ) / Real.pi) ^ 2 /
    (16 * (n : ℝ) ^ 2)

/-- Claim 13640: the exact second-column finite difference, the ratio of the
first two Neville multipliers, and the second multiplier's Lambert scale. -/
def claim13640 : Prop :=
  ∀ (α b : ℝ),
    let A : ℝ := b - α * thetaMoment 0
    let D : ℝ := thetaMoment 0 - α * thetaMoment 1
    let γ : ℝ := α * thetaMoment 1 / D - b / A
    0 < A → D ≠ 0 → γ ≠ 0 →
      IsEquivalent atTop
        (fun n : ℕ =>
          normalizedSecondColumn α b n -
            normalizedSecondColumn α b (n - 1))
        (fun n : ℕ => -(D * γ) / (A * (n : ℝ) ^ 2)) ∧
      Tendsto
        (fun n : ℕ =>
          secondBoundaryMultiplier α b n /
            firstBoundaryMultiplier α b n)
        atTop (𝓝 (1 : ℝ)) ∧
      IsEquivalent atTop
        (fun n : ℕ => secondBoundaryMultiplier α b n)
        (fun n : ℕ => lambertBoundaryScale n)

end

end MathlibPlus.Open.ResearchFormalization.O0153.Claim13640
