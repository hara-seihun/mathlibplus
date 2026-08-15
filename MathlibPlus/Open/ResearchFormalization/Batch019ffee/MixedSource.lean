import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- Claim 18401: the first mixed source inequality, including the
nonzero-denominator condition required by its division-based formulation. -/
def firstMixedSourceInequality
    (a₀ a₁ a₂ c₀ c₁ c₂ c₃ : ℝ) : Prop :=
  a₀ ≠ 0 ∧
    (1 / a₀) *
        Matrix.det (fun i j =>
          ![![a₀, a₁, a₂], ![c₀, c₁, c₂], ![c₁, c₂, c₃]] i j) > 0

end MathlibPlus.Open.ResearchFormalization
