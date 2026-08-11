import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim13841

/-- A differentiable coefficient jet has the displayed nearest-neighbor flow. -/
theorem nearestNeighbor_timeJet_flow_claim13841
    (c : ℕ → ℝ → ℝ)
    (h : ∀ (j : ℕ) (t : ℝ), HasDerivAt (c j) (c (j + 1) t) t) :
    ∀ (j : ℕ) (t : ℝ), deriv (c j) t = c (j + 1) t := by
  intro j t
  exact (h j t).deriv

end MathlibPlus.Analysis.Claim13841
