import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

def integrationTailEnclosure : Prop :=
  let shell : ℕ → ℝ → ℝ := fun n u =>
    let x_n : ℝ := Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u)
    2 * Real.exp (u / 2) * x_n * (2 * x_n - 3) * Real.exp (-x_n)
  let Φ : ℝ → ℝ := fun u =>
    ∑' n : {n : ℕ // 0 < n}, shell n.1 |u|
  let A_tail : ℝ → ℝ := fun y =>
    ∫ d in Set.Ici (3 : ℝ), Φ (y + d) * Φ (y - d)
  let J_tail : ℝ → ℝ := fun y =>
    ∫ d in Set.Ici (3 : ℝ), d ^ 2 * Φ (y + d) * Φ (y - d)
  let sample : ℕ → ℝ := fun j => 2 * (j : ℝ) / 25
  let C : ℝ := 4 * Real.pi ^ 2 / (1 - 16 * Real.exp (-3 * Real.pi))
  (∀ j : ℕ, 0 ≤ j → j ≤ 8 → ∀ d : ℝ, 3 ≤ d →
      Φ (d + sample j) * Φ (d - sample j) ≤
        C ^ 2 * Real.exp (9 * d - 2 * Real.pi * Real.exp (2 * d))) ∧
    (∀ j : ℕ, 0 ≤ j → j ≤ 8 →
      A_tail (sample j) ≤ (4.6 : ℝ) * (10 : ℝ)⁻¹ ^ 1090) ∧
    (∀ j : ℕ, 0 ≤ j → j ≤ 8 →
      J_tail (sample j) ≤ (4.2 : ℝ) * (10 : ℝ)⁻¹ ^ 1089)

end MathlibPlus.Open.Analysis
