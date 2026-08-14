import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open MeasureTheory

noncomputable section

def translationAutocorrelation (w : ℝ → ℝ) (D : ℝ) : ℝ :=
  ∫ v : ℝ, w (v - D) * w (v + D)

def relativePositionSecondMoment (w : ℝ → ℝ) (D : ℝ) : ℝ :=
  ∫ v : ℝ, v ^ 2 * w (v - D) * w (v + D)

end

end MathlibPlus.Open.ResearchFormalization
