import MathlibPlus.Open.Analysis.StieltjesContext

namespace MathlibPlus.Open.Analysis

def sharpFixedTemplateTwoSidedBounds : Prop :=
  stieltjesContext ∧
    ∀ s : ℝ, 1 < s →
      stieltjesAlpha / s ^ 2 <
          (deriv riemannZeta (s : ℂ)).re + 1 / (s - 1) ^ 2 ∧
        (deriv riemannZeta (s : ℂ)).re + 1 / (s - 1) ^ 2 <
          151 * stieltjesAlpha / (151 + (s - 1) ^ 2)

end MathlibPlus.Open.Analysis
