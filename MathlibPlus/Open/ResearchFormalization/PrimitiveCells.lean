import Mathlib

noncomputable section

open MeasureTheory
open scoped BigOperators Interval Matrix

namespace MathlibPlus.Open.ResearchFormalization

/-- Exact graph of the primitive first-bump definitions. -/
def primitiveFirstBump (A phi : ℝ → ℝ) : Prop :=
  ∀ v : ℝ, 0 ≤ v →
    A v = Real.pi * Real.exp (2 * v) ∧
      phi v = 2 * Real.exp (v / 2) * A v * (2 * A v - 3) * Real.exp (-A v)

/-- Exact formula for the folded cell density. -/
def foldedCellDensity (K : ℕ → ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (u : ℝ), 0 ≤ u →
    K n u =
      ∫ x in (n : ℝ)..((n : ℝ) + 1),
        x * (x - (n : ℝ)) *
          (Real.exp (-5 * u / 2 - Real.pi * x ^ 2 * Real.exp (-2 * u)) +
            Real.exp (5 * u / 2 - Real.pi * x ^ 2 * Real.exp (2 * u)))

/-- Exact formula for the completed cell coefficients. -/
def completedCellCoefficients
    (C : ℝ) (K : ℕ → ℝ → ℝ) (B : ℕ → ℕ → ℝ) : Prop :=
  0 < C ∧
    ∀ (n j : ℕ),
      B n j =
        C / (Nat.factorial (2 * j) : ℝ) *
          (∫ u in Set.Ici (0 : ℝ), u ^ (2 * j) * K n u)


end MathlibPlus.Open.ResearchFormalization
