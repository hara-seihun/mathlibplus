import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch.Shell

open scoped BigOperators
open MeasureTheory

noncomputable section

def dividedShellMoment (n k : ℕ) : ℝ :=
  (1 / ((Nat.factorial (2 * k) : ℕ) : ℝ)) *
    (∫ u : ℝ in Set.Ioi (0 : ℝ),
      2 * Real.exp (u / 2 - Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u)) * u ^ (2 * k))

def claim42894 : Prop :=
  ∀ (n k : ℕ), 1 ≤ n → k ≤ 3 →
    dividedShellMoment n k =
      (1 / ((Nat.factorial (2 * k) : ℕ) : ℝ)) *
        (∫ u : ℝ in Set.Ioi (0 : ℝ),
          2 * Real.exp (u / 2 - Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u)) * u ^ (2 * k))

def claim42895 : Prop :=
  ∀ (n k : ℕ), 1 ≤ n → k ≤ 3 →
    dividedShellMoment n k ≤
      (2 * Real.exp (-Real.pi * (n : ℝ) ^ 2)) /
        (2 * Real.pi * (n : ℝ) ^ 2 - (1 / 2 : ℝ)) ^ (2 * k + 1)

end
end MathlibPlus.Open.ResearchFormalizationBatch.Shell
