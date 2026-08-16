import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.Analysis

/-- The explicit unit long-wave packet on complex `L²(ℝ, dx)`. -/
def explicitLongWavePacket_claim14178 : Prop :=
  ∀ (a θ r : ℝ) (z : ℂ) (R : ℝ),
    a ≠ 0 →
    0 ≤ r →
    z = (r : ℂ) * Complex.exp (Complex.I * θ) →
    R > |a| / 2 →
    ∃ f_R : MeasureTheory.Lp ℂ 2 (volume : Measure ℝ),
      (∀ᵐ x ∂(volume : Measure ℝ),
        (f_R : ℝ → ℂ) x =
          ((Real.rpow (2 * R) (-1 / 2 : ℝ)) : ℂ) *
            Complex.exp (Complex.I * (θ * x / a)) *
              Set.indicator (Set.Icc (-R) R) (fun _ : ℝ => (1 : ℂ)) x) ∧
        ‖f_R‖ = 1

end MathlibPlus.Open.Analysis
