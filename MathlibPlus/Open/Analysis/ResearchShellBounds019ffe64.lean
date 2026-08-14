import Mathlib

namespace MathlibPlus.Open.Analysis.ResearchFormalizationBatch019ffe64

open MeasureTheory

noncomputable section

/-- The real integral appearing in the `m`-th primitive shell moment. -/
def shellMomentFormula (m j : ℕ) : ℝ :=
  (2 / (Nat.factorial (2 * j) : ℝ)) *
    ∫ u in Set.Ioi (0 : ℝ),
      Real.exp (u / 2 - Real.pi * (m : ℝ) ^ 2 * Real.exp (2 * u)) *
        u ^ (2 * j)

/-- The analytic shell generating function. -/
def shellGeneratingFunction (m : ℕ) (z : ℂ) : ℂ :=
  ∫ u in Set.Ioi (0 : ℝ),
    (Real.exp (u / 2 - Real.pi * (m : ℝ) ^ 2 * Real.exp (2 * u)) : ℂ) *
      Complex.cosh ((u : ℂ) * Complex.sqrt z)

/-- The primitive moment formula and its generating function. -/
def primitiveMomentShellClaim50493 : Prop :=
  ∃ t : ℕ → ℕ → ℝ,
    (∀ m j : ℕ, t m j = shellMomentFormula m j) ∧
      (∀ (m : ℕ) (z : ℂ),
        HasSum (fun j : ℕ => (t m j : ℂ) * z ^ j)
          (2 * shellGeneratingFunction m z))

/-- The uniform circle estimate for the shell generating function. -/
def primitiveShellBoundClaim50499 : Prop :=
  ∀ (m : ℕ) (R : ℝ),
    0 < R →
    2 * Real.pi * (m : ℝ) ^ 2 > Real.sqrt R + 1 / 2 →
      ∀ z : ℂ, ‖z‖ = R →
        ‖shellGeneratingFunction m z‖ ≤
          2 * Real.exp (-Real.pi * (m : ℝ) ^ 2) /
            (2 * Real.pi * (m : ℝ) ^ 2 - Real.sqrt R - 1 / 2)

end

end MathlibPlus.Open.Analysis.ResearchFormalizationBatch019ffe64
