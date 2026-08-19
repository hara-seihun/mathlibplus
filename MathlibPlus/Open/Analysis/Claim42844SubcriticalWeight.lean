import Mathlib

namespace MathlibPlus.Open.Analysis.Claim42844

/-- Exact subcritical-weight blindness inequality on the displayed complex
carrier. -/
def claim42844_subcriticalWeightBlindness : Prop :=
  ∀ (ρ W : ℂ) (x ε : ℝ),
    ρ.re < 1 →
    0 < x →
    ‖W‖ ≤ Real.exp (ε * x) →
    ε < 1 - (ρ / (ρ - 1)).re →
    ‖W * Complex.exp ((x : ℂ) * (ρ / (ρ - 1) - 1))‖ < 1

end MathlibPlus.Open.Analysis.Claim42844
