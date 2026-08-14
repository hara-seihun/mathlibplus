import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The scalar from the polyharmonic saddle formula, on positive integers. -/
noncomputable def polyharmonicSigma (m : ℕ) : ℝ :=
  if 0 < m then
    (2 * (m : ℝ) - 1) *
        Real.rpow (2 * (m : ℝ))
          (-(2 * (m : ℝ)) / (2 * (m : ℝ) - 1)) *
      Real.sin (Real.pi / (4 * (m : ℝ) - 2))
  else 0

/-- Large-order scalar limit and its stated asymptotic. -/
def largeOrderScalarLimit_claim4542 : Prop :=
  Filter.Tendsto
      (fun k : ℕ => (k : ℝ) * polyharmonicSigma k)
      Filter.atTop (nhds (Real.pi / 4)) ∧
    Asymptotics.IsEquivalent Filter.atTop polyharmonicSigma
      (fun k : ℕ => Real.pi / (4 * (k : ℝ)))

end MathlibPlus.Open.Analysis
