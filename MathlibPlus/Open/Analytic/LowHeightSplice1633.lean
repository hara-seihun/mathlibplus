import Mathlib

namespace MathlibPlus.Open.Analytic

noncomputable def lowHeightH : ℝ := 3 * (10 : ℝ) ^ 12

noncomputable def lowHeightZeroFree : Prop :=
  ∀ t : ℝ, 2 ≤ t → t < lowHeightH →
    ∀ σ : ℝ,
      1 - 1 / (4.852 * Real.log t) < σ →
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0

def lowHeightSplice : Prop :=
  lowHeightZeroFree ∧
    1 / 2 + 0.20265 <
      1 - 1 / (4.852 * Real.log 2)

end MathlibPlus.Open.Analytic
