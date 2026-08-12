import Mathlib

open Filter Asymptotics
open scoped Topology

namespace MathlibPlus.Open.Asymptotics

/-- Claim 15199: the principal positive Lambert-W branch has unit scale
quotients along the two displayed index subsequences. -/
def lambertWQuotientScaleComparison_15199 : Prop :=
  ∃ W0 : ℝ → ℝ,
    (∀ x : ℝ, 0 < x → 0 < W0 x ∧ W0 x * Real.exp (W0 x) = x) ∧
    Tendsto
      (fun n : ℕ =>
        W0 (((2 * n - 1 : ℕ) : ℝ) / (2 * Real.pi)) /
          W0 (((4 * n : ℕ) : ℝ) / (2 * Real.pi)))
      atTop (𝓝 1) ∧
    Tendsto
      (fun n : ℕ =>
        W0 (((2 * n : ℕ) : ℝ) / (2 * Real.pi)) /
          W0 (((4 * n : ℕ) : ℝ) / (2 * Real.pi)))
      atTop (𝓝 1)

end MathlibPlus.Open.Asymptotics
