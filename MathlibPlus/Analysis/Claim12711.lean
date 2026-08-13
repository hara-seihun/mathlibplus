import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim12711

/-- The constant-product conjugacy identity forces the affine coefficient to
vanish, so it cannot come from a nonconstant affine change of parameter. -/
theorem noNonconstantAffineConjugacy_claim12711
    {a b : ℝ}
    (h : ∀ s : ℝ, (a * (1 - s) + b) * (a * s + b) = 4 * Real.pi ^ 2) :
    a = 0 := by
  have h0 := h 0
  have hm1 := h (-1)
  nlinarith [sq_nonneg a]

end MathlibPlus.Analysis.Claim12711
