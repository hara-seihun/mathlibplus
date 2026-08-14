import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization

noncomputable def foldedArithmeticCellDensity (n : ℤ) (u : ℝ) : ℝ :=
  ∫ x in (n : ℝ)..((n : ℝ) + 1),
    x * (x - (n : ℝ)) *
      (Real.exp (-5 * u / 2 - Real.pi * x ^ 2 * Real.exp (-2 * u)) +
        Real.exp (5 * u / 2 - Real.pi * x ^ 2 * Real.exp (2 * u)))

noncomputable def foldedArithmeticCellMoment (n : ℤ) (j : ℕ) : ℝ :=
  ∫ u in Set.Ici (0 : ℝ),
    u ^ (2 * j) * foldedArithmeticCellDensity n u

def foldedArithmeticUnitCellDensityClaim : Prop :=
  (∀ n : ℤ, ∀ u : ℝ, 0 ≤ u →
    foldedArithmeticCellDensity n u =
      ∫ x in (n : ℝ)..((n : ℝ) + 1),
        x * (x - (n : ℝ)) *
          (Real.exp (-5 * u / 2 - Real.pi * x ^ 2 * Real.exp (-2 * u)) +
            Real.exp (5 * u / 2 - Real.pi * x ^ 2 * Real.exp (2 * u)))) ∧
  (∀ n : ℤ, ∀ j : ℕ,
    foldedArithmeticCellMoment n j =
      ∫ u in Set.Ici (0 : ℝ),
        u ^ (2 * j) * foldedArithmeticCellDensity n u)

end MathlibPlus.Open.ResearchFormalization
