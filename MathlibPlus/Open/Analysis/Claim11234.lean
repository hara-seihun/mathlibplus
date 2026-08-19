import MathlibPlus.Open.Analysis.Claim11235_11240_11241

namespace MathlibPlus.Analysis.Claim11234

open MathlibPlus.Open.Analysis

/-- Claim 11234: the same integer hold is strictly positive on both
coordinate axes, with its complex evaluations retained explicitly. -/
def strictPositivityAxes : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    ∀ x t : ℝ,
      (qₘ m (x : ℂ) = ((1 + x ^ (4 * m) : ℝ) : ℂ) ∧
        0 < 1 + x ^ (4 * m)) ∧
      (qₘ m (criticalAxisPoint t) =
          ((1 + t ^ (4 * m) : ℝ) : ℂ) ∧
        0 < 1 + t ^ (4 * m))

end MathlibPlus.Analysis.Claim11234
