import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

def scalarConditionalVarianceCounterexample : Prop :=
  let shell : ℕ → ℝ → ℝ := fun n u =>
    let x_n : ℝ := Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u)
    2 * Real.exp (u / 2) * x_n * (2 * x_n - 3) * Real.exp (-x_n)
  let Φ : ℝ → ℝ := fun u =>
    ∑' n : {n : ℕ // 0 < n}, shell n.1 |u|
  let A : ℝ → ℝ := fun y =>
    ∫ d : ℝ, Φ (y + d) * Φ (y - d)
  let J : ℝ → ℝ := fun y =>
    ∫ d : ℝ, d ^ 2 * Φ (y + d) * Φ (y - d)
  let V : ℝ → ℝ := fun y => J y / A y
  let density : ℝ → ℝ → ℝ := fun y d =>
    Φ (y + d) * Φ (y - d) / A y
  let positiveDefinite : Prop :=
    ∀ n : ℕ, ∀ t : Fin n → ℝ, ∀ a : Fin n → ℝ,
      0 ≤ ∑ i : Fin n, ∑ j : Fin n,
        a i * V |t i - t j| * a j
  let sample : Fin 9 → ℝ := fun j => 2 * (j.1 : ℝ) / 25
  let q : Fin 9 → ℝ :=
    ![-31335, 178814, -488808, 841294, -1000000, 841294, -488808, 178814, -31335]
  let M : Matrix (Fin 9) (Fin 9) ℝ := fun i j => V |sample i - sample j|
  let qForm : ℝ := ∑ i : Fin 9, ∑ j : Fin 9, q i * M i j * q j
  (∀ y d : ℝ, 0 ≤ density y d) ∧
    (∀ y : ℝ, 0 < A y) ∧
    (∀ y d : ℝ, density y d = density y (-d)) ∧
    qForm < 0 ∧
    ¬ positiveDefinite

end MathlibPlus.Open.Analysis
