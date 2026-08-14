import Mathlib

open scoped Topology
open Filter

namespace MathlibPlus.Open.Analysis.AdmittedBatchC0299

noncomputable section

/-- R-0299.4179, written as a sequential uniform asymptotic statement. -/
def uniformPoissonModerateDeviation : Prop :=
  ∀ (d M : ℝ), 0 < d → 0 < M →
    ∀ (x : ℕ → ℝ) (r : ℕ → ℕ),
      Tendsto x atTop atTop →
      (∀ᶠ n : ℕ in atTop, 0 < d * x n) →
      (∀ᶠ n : ℕ in atTop,
        |(r n : ℝ) - d * x n| ≤
          M * Real.sqrt (d * x n * Real.log (x n))) →
      Tendsto
        (fun n : ℕ =>
          Real.exp (-(d * x n)) * (d * x n) ^ (r n) /
              (Nat.factorial (r n) : ℝ) *
            Real.sqrt (2 * Real.pi * (d * x n)) *
            Real.exp (((r n : ℝ) - d * x n) ^ 2 /
              (2 * d * x n)))
        atTop (𝓝 1)

end

end MathlibPlus.Open.Analysis.AdmittedBatchC0299
