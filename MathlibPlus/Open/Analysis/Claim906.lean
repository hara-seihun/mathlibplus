import Mathlib

/-!
# Claim 906: denominator-comparison margin

The packet's `σ₀` is expanded from its source definitions: `A_aux = 1/4.8594`,
`H = 3 * 10^12`, `K = 16`, and `T₀ = 10^10`.  Thus this registry node does
not replace the source parameter by an unconstrained real.  The certified
real-log inequality remains a registry proposition until a kernel-checked
numerical proof is admitted.
-/

namespace MathlibPlus.Open.Analysis

/-- Claim 906: `d₀ - c₀ > 0`, and hence the strict comparison after positive
integer scaling, for the source's auxiliary denominator parameters. -/
def claim906_denominatorComparisonMargin : Prop :=
  let Aaux : ℝ := 1 / (4.8594 : ℝ)
  let H : ℝ := 3 * 10 ^ 12
  let K : ℝ := 16
  let T₀ : ℝ := 10 ^ 10
  let σ₀ : ℝ := 1 - Aaux / Real.log (K * H + T₀)
  let d₀ : ℝ := 2 * σ₀ - 1
  let c₀ : ℝ := 151 / 153
  d₀ - c₀ > 0 ∧
    ∀ m : ℕ, 0 < m → c₀ * (m : ℝ) < d₀ * (m : ℝ)

end MathlibPlus.Open.Analysis
