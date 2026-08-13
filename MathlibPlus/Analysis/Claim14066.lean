import Mathlib

open Filter
open scoped Topology

namespace MathlibPlus.Analysis

/-- Local factorization of an analytic function at a simple zero (claim 14066). -/
theorem localFactorizationAtSimpleZero_claim14066 {F : ℂ → ℂ} {ρ : ℂ}
    (hF : AnalyticAt ℂ F ρ) (hzero : F ρ = 0)
    (hsimple : deriv F ρ ≠ 0) (_hnotident : ¬ ∀ s, F s = 0) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G ρ ∧ G ρ ≠ 0 ∧
      ∀ᶠ s in 𝓝 ρ, F s = (s - ρ) * G s := by
  have horder : analyticOrderAt F ρ = 1 :=
    hF.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero hsimple
  obtain ⟨G, hG, hG0, hfactor⟩ :=
    (hF.analyticOrderAt_eq_natCast (n := 1)).1 horder
  refine ⟨G, hG, hG0, ?_⟩
  simpa [pow_one, smul_eq_mul] using hfactor

end MathlibPlus.Analysis
