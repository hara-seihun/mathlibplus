import Mathlib

namespace MathlibPlus.Open.Analysis

open scoped BigOperators Interval

/-- Cesàro convergence on the nonnegative half-line. -/
def cesaroMean (f : ℝ → ℝ) (limit : ℝ) : Prop :=
  Filter.Tendsto
    (fun T : ℝ => (1 / T) * ∫ t in (0)..T, f t)
    Filter.atTop (nhds limit)

/--
Claim 12497: a nonzero real finite trigonometric polynomial with distinct
nonzero frequencies has zero Cesàro mean, positive mean square, and positive
and negative subsequences bounded away from zero.
-/
def zeroFrequencyFreeTrigonometricPacketsChangeSign : Prop :=
  ∀ (frequencies : Finset ℝ) (a b : ℝ → ℝ),
    0 ∉ frequencies →
    let f : ℝ → ℝ := fun t =>
      frequencies.sum (fun ω =>
        a ω * Real.cos (ω * t) + b ω * Real.sin (ω * t))
    (∃ t : ℝ, f t ≠ 0) →
      cesaroMean f 0 ∧
        (∃ meanSquare : ℝ,
          0 < meanSquare ∧ cesaroMean (fun t => f t ^ 2) meanSquare) ∧
        (∃ ε : ℝ,
          0 < ε ∧
            ∃ p q : ℕ → ℝ,
              Filter.Tendsto p Filter.atTop Filter.atTop ∧
                Filter.Tendsto q Filter.atTop Filter.atTop ∧
                Filter.Eventually (fun n => ε ≤ f (p n)) Filter.atTop ∧
                Filter.Eventually (fun n => f (q n) ≤ -ε) Filter.atTop)

end MathlibPlus.Open.Analysis
