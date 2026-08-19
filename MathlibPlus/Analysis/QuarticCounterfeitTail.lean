import Mathlib

namespace MathlibPlus.Analysis

noncomputable section

/-- Claim 3601: the quartic counterfeit logarithmic-derivative magnitude has
its exact reciprocal-scale bounds once `0 ≤ R ≤ x` and `x > 0`. -/
def quarticCounterfeitTail : Prop :=
  ∀ R x : ℝ, 0 < x → 0 ≤ R → R ≤ x →
    let qR : ℝ := 4 * x ^ 3 / (R ^ 4 + x ^ 4)
    2 / x ≤ qR ∧
      qR ≤ 4 / x ∧
      2 ≤ x * qR ∧
      x * qR ≤ 4

end

end MathlibPlus.Analysis
