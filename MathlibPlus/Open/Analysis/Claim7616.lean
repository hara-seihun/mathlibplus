import Mathlib

namespace MathlibPlus.Open.Analysis.Claim7616

/-- Claim 7616: the support line at an off-axis coordinate exceeds the
axis barrier by `2 * beta^2`. -/
def offAxisZeroRaisesSupportEnvelopeClaim7616 : Prop :=
  ∀ (β γ : ℝ), β ≠ 0 →
    let r := β ^ 2 + γ ^ 2
    let b := -r + 2 * β ^ 2
    let q := r
    q * Real.log r + b =
        (q * Real.log q - q) + 2 * β ^ 2 ∧
      q * Real.log r + b > q * Real.log q - q

end MathlibPlus.Open.Analysis.Claim7616
