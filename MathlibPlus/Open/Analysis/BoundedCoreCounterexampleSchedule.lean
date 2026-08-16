import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The positive-index bounded-core schedule, including its pointwise and
visibility limits and the failure of a locally uniform entire limit. -/
def boundedCoreCounterexampleSchedule : Prop :=
  let k : ℕ+ → ℕ := fun n => (n : ℕ)
  let L : ℕ+ → ℝ := fun n => (4 : ℝ) ^ (n : ℕ)
  let α : ℕ+ → ℝ := fun n => (4 : ℝ)⁻¹ ^ (n : ℕ)
  let ε : ℕ+ → ℝ := fun n => Real.exp (-2 * L n)
  let M : ℕ+ → ℂ → ℂ := fun n z =>
    Complex.exp (-((α n : ℂ) * z ^ (2 * k n)))
  let Mreal : ℕ+ → ℝ → ℝ := fun n x =>
    Real.exp (-((x ^ 2 / 4) ^ (n : ℕ)))
  let a : ℕ+ → ℝ := fun n =>
    Real.rpow (α n) (1 / (2 * (k n : ℝ)))
  let S : ℕ+ → ℝ := fun n =>
    Real.rpow (L n / α n) (1 / (2 * (k n : ℝ)))
  let V : ℕ+ → ℝ := fun n =>
    Real.rpow (Real.log ((ε n)⁻¹) / α n) (1 / (2 * (k n : ℝ)))
  let D : ℕ+ → ℝ := fun n =>
    Real.log (ε n) + α n * (5 : ℝ) ^ (2 * k n)
  let f : ℝ → ℝ := fun x =>
    if |x| < 2 then 1 else if |x| = 2 then Real.exp (-1) else 0
  (∀ n, k n = (n : ℕ)) ∧
  (∀ n, L n = (4 : ℝ) ^ (n : ℕ)) ∧
  (∀ n, α n = (4 : ℝ)⁻¹ ^ (n : ℕ)) ∧
  (∀ n, ε n = Real.exp (-2 * L n)) ∧
  (∀ n, a n = (1 / 2 : ℝ)) ∧
  (∀ n, S n = 4) ∧
  (∀ (n : ℕ+) (x : ℝ), M n (x : ℂ) = (Mreal n x : ℂ)) ∧
  (∀ x, |x| < 2 →
    Filter.Tendsto (fun n => Mreal n x) Filter.atTop (nhds 1)) ∧
  (∀ x, |x| > 2 →
    Filter.Tendsto (fun n => Mreal n x) Filter.atTop (nhds 0)) ∧
  (∀ x, |x| = 2 →
    (∀ n, Mreal n x = Real.exp (-1)) ∧
    Filter.Tendsto (fun n => Mreal n x) Filter.atTop (nhds (Real.exp (-1)))) ∧
  (∀ x,
    Filter.Tendsto (fun n => Mreal n x) Filter.atTop (nhds (f x))) ∧
  (∀ x, |x| < 2 → f x = 1) ∧
  (∀ x, |x| > 2 → f x = 0) ∧
  (∀ x, |x| = 2 → f x = Real.exp (-1)) ∧
  ¬Continuous f ∧
  (¬ (∃ F : ℂ → ℂ,
    Differentiable ℂ F ∧
    ∀ R : ℝ, 0 < R →
      ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ+, ∀ n : ℕ+, N ≤ n →
          ∀ z : ℂ, ‖z‖ ≤ R → ‖M n z - F z‖ < δ)) ∧
  (∀ n,
    V n = 4 * Real.rpow (2 : ℝ) (1 / (2 * (n : ℝ)))) ∧
  Filter.Tendsto V Filter.atTop (nhds 4) ∧
  (∀ n,
    D n = -2 * (4 : ℝ) ^ (n : ℕ) + ((25 : ℝ) / 4) ^ (n : ℕ)) ∧
  Filter.Tendsto D Filter.atTop Filter.atTop

end MathlibPlus.Open.Analysis
