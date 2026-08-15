import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

/-- Full convergence splits into the positive head and tail conditions. -/
def fullConvergenceSplitsIntoPositiveHeadAndTail : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 →
    let A : ℕ → ℝ := fun n =>
      ∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ)
    let R : ℕ → ℕ → ℝ := fun n j =>
      (j : ℝ) * A n +
        ∑ k ∈ Finset.Icc (n + 1) j,
          (ArithmeticFunction.moebius k : ℝ) * ((j / k : ℕ) : ℝ)
    let s : ℕ → ℝ → ℝ := fun n α =>
      (1 / (2 * α)) *
        ∑' j : ℕ,
          if 1 ≤ j then
            (R n j) ^ 2 *
              (Real.rpow (j : ℝ) (-2 * α) -
                Real.rpow ((j + 1 : ℕ) : ℝ) (-2 * α))
          else 0
    Filter.Tendsto (fun n => s n α) Filter.atTop (nhds 0) ↔
      (Asymptotics.IsLittleO Filter.atTop A
          (fun n => Real.rpow (n : ℝ) (α - 1)) ∧
        Asymptotics.IsLittleO Filter.atTop
          (fun n =>
            ∑' j : ℕ,
              if n < j then
                (R n j) ^ 2 * Real.rpow (j : ℝ) (-2 * α - 1)
              else 0)
          (fun _ => (1 : ℝ)))

end MathlibPlus.Open.Analysis
