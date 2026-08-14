import Mathlib

namespace MathlibPlus.Open.Analysis

open Filter
open scoped Topology

/-- Uniform convergence on each compact subset of the complex plane. -/
def locallyUniformlyOnCompacts
    (F : ℕ+ → ℂ → ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ K : Set ℂ, IsCompact K →
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ+ in atTop, ∀ z ∈ K, ‖F n z - f z‖ < ε

/-- The explicit bounded-core schedule and its asserted limiting behavior. -/
def boundedCoreSchedule : Prop :=
  let k : ℕ+ → ℕ := fun n => (n : ℕ)
  let L : ℕ+ → ℝ := fun n => (4 : ℝ) ^ (n : ℕ)
  let α : ℕ+ → ℝ := fun n => (4 : ℝ) ^ (-(n : ℤ))
  let a : ℕ+ → ℝ := fun _ => (1 : ℝ) / 2
  let S : ℕ+ → ℝ := fun _ => 4
  let M : ℕ+ → ℂ → ℂ :=
    fun n z => Complex.exp (-((α n : ℂ) * z ^ (2 * k n)))
  let ε : ℕ+ → ℝ := fun n => Real.exp (-2 * L n)
  let V : ℕ+ → ℝ :=
    fun n => 4 * Real.rpow 2 (1 / (2 * (n : ℝ)))
  (∀ n : ℕ+, k n = (n : ℕ)) ∧
    (∀ n : ℕ+, L n = (4 : ℝ) ^ (n : ℕ)) ∧
    (∀ n : ℕ+, α n = (4 : ℝ) ^ (-(n : ℤ))) ∧
    (∀ n : ℕ+, a n = (1 : ℝ) / 2 ∧ S n = 4) ∧
    (∀ n : ℕ+, ∀ z : ℂ,
      M n z = Complex.exp (-((α n : ℂ) * z ^ (2 * k n)))) ∧
    (∀ n : ℕ+, ∀ x : ℝ,
      M n (x : ℂ) = Complex.exp (-(((x : ℂ) ^ 2 / 4) ^ (n : ℕ)))) ∧
    (∀ n : ℕ+, ε n = Real.exp (-2 * L n)) ∧
    (∀ n : ℕ+, V n = 4 * Real.rpow 2 (1 / (2 * (n : ℝ)))) ∧
    (∀ x : ℝ, |x| < 2 →
      Tendsto (fun n : ℕ+ => M n (x : ℂ)) atTop (𝓝 (1 : ℂ))) ∧
    (∀ x : ℝ, |x| > 2 →
      Tendsto (fun n : ℕ+ => M n (x : ℂ)) atTop (𝓝 (0 : ℂ))) ∧
    (¬ ∃ f : ℂ → ℂ,
      Differentiable ℂ f ∧ locallyUniformlyOnCompacts M f) ∧
    Tendsto V atTop (𝓝 4) ∧
    Tendsto
      (fun n : ℕ+ => -2 * (4 : ℝ) ^ (n : ℕ) + ((25 : ℝ) / 4) ^ (n : ℕ))
      atTop atTop

end MathlibPlus.Open.Analysis
