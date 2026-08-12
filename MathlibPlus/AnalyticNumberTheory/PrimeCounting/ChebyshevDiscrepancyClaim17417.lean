import Mathlib.NumberTheory.Chebyshev

namespace MathlibPlus.AnalyticNumberTheory.PrimeCounting

/-- Claim 17417's discrepancy, with its stated domain `T ≥ 0` represented by
`Set.Ici (0 : ℝ)`. -/
noncomputable def criticallyNormalizedChebyshevDiscrepancy_claim17417
    : Set.Ici (0 : ℝ) → ℝ := fun T =>
  Real.exp (-T.1 / 2) * (Chebyshev.psi (Real.exp T.1) - Real.exp T.1)

end MathlibPlus.AnalyticNumberTheory.PrimeCounting
