import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.O0356

/-- Claim 15662: Record 27's false-RH rate wedge together with the verified
height inequalities gives the strict chain `0 < κ < d < 1/H²`. -/
def claim15662_verifiedHeightFalseRHWedge : Prop :=
  ∀ (β γ H d κ : ℝ),
    (1 / 2 : ℝ) < β →
      β < 1 →
        0 < d →
          κ = (2 * β - 1) * d →
            0 < H ^ 2 →
              H ^ 2 < γ ^ 2 →
                d = 1 / ((β - 1) ^ 2 + γ ^ 2) →
                  0 < κ ∧ κ < d ∧ d < 1 / H ^ 2

end MathlibPlus.Open.ResearchFormalization.O0356
