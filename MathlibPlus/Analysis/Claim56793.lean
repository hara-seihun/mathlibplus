import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim56793

/-- At a real double zero, the first-order collision projector vanishes. -/
theorem firstOrderCollisionProjector_vanishes
    (A H : ℝ → ℂ) (u p : ℝ) (x : ℝ)
    (_hp : 0 < p)
    (_hlog : deriv A x / A x = (u : ℂ) + (p : ℂ) * Complex.I)
    (hH : H x = 0)
    (hH' : deriv H x = 0) :
    H x + (Complex.I / (p : ℂ)) * deriv H x = 0 := by
  rw [hH, hH']
  simp

end MathlibPlus.Analysis.Claim56793
