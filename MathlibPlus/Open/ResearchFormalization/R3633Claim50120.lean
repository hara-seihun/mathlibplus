import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R3633Claim50120

noncomputable section

/-- Claim 50120: the standalone Gaussian tail estimate for every positive
integer lower index. No theta-shell operator estimate is included. -/
def claim50120 : Prop :=
  ∀ (M : ℕ),
    0 < M →
      ∑' m : {m : ℕ // M ≤ m},
          Real.exp (-Real.pi * (m.1 : ℝ) ^ 2) ≤
        Real.exp (-Real.pi * (M : ℝ) ^ 2) *
          (1 + 1 / (2 * Real.pi * (M : ℝ)))

end
end MathlibPlus.Open.ResearchFormalization.R3633Claim50120
