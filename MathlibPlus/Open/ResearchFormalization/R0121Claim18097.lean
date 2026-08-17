import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0121

noncomputable section

/-- Claim 18097: every positive even central derivative of the exact
normalized gamma carrier diverges at positive infinity. -/
def claim18097_evenCentralDerivativesGrowWithoutBound : Prop :=
  let M : ℝ → ℝ := fun t =>
    Real.rpow Real.pi (t / 2) * Real.Gamma ((5 : ℝ) / 4 - t / 2) /
      Real.Gamma ((5 : ℝ) / 4)
  let H : ℝ → ℝ → ℝ := fun x t => Real.rpow x t * M t
  ∀ j : ℕ, 1 ≤ j →
    Filter.Tendsto
      (fun x : ℝ => (deriv^[2 * j] (H x)) 0)
      Filter.atTop Filter.atTop

end

end MathlibPlus.Open.ResearchFormalization.R0121
