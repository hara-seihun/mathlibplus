import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace MathlibPlus.Analysis

/-- Claim 17961: center/relative spectral coordinates and their inverse. -/
theorem spectralCenterRelativeRotation_claim17961
    {K : Type*} [Field K] [CharZero K] (σ₁ σ₂ : K) :
    let Sigma := σ₁ + σ₂
    let tau := σ₁ - σ₂
    σ₁ = (Sigma + tau) / 2 ∧ σ₂ = (Sigma - tau) / 2 := by
  dsimp
  constructor <;> ring

/-- Claim 8838: the within-pair gauge stagger after substituting
`R_j = log (8π a_j) + W_j` at the two indices of a pair. -/
theorem exactWithinPairGaugeStagger_claim8838
    (k : ℕ) (r s W : ℕ → ℝ)
    (hr : 0 < r (k - 1)) (hs : 0 < s k) :
    (Real.log (8 * Real.pi * s k) + W (2 * k)) -
        (Real.log (8 * Real.pi * r (k - 1)) + W (2 * k - 1)) =
      Real.log (s k / r (k - 1)) + W (2 * k) - W (2 * k - 1) := by
  have hconst : (8 : ℝ) * Real.pi ≠ 0 := by positivity
  have hr0 : r (k - 1) ≠ 0 := ne_of_gt hr
  have hs0 : s k ≠ 0 := ne_of_gt hs
  rw [Real.log_mul hconst hs0, Real.log_mul hconst hr0,
    Real.log_div hs0 hr0]
  ring

end MathlibPlus.Analysis
