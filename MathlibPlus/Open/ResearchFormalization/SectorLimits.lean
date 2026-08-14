import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- The Schoenberg sector angle from the admitted fixed-order claim. -/
private def sectorSchoenbergAngle (N m : ℕ) : ℝ :=
  Real.pi * (m : ℝ) / ((N + m - 1 : ℕ) : ℝ)

/-- Claim 10262: a fixed positive order has vanishing sector angle, so it
cannot supply a positive degree-uniform lower bound. -/
def claim10262 : Prop :=
  ∀ m : ℕ, 0 < m →
    Filter.Tendsto (fun N : ℕ => sectorSchoenbergAngle N m) Filter.atTop (nhds 0) ∧
      ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, sectorSchoenbergAngle N m < δ

end MathlibPlus.Open.ResearchFormalizationBatch
