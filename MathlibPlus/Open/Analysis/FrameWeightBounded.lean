import Mathlib

namespace MathlibPlus.Open.Analysis

open Filter

/-- The Fourier multiplier from the packet's repair context. -/
noncomputable def frameMultiplier (ε t : ℝ) : ℂ :=
  ((((-1 / 2 + ε : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2) *
    Complex.Gamma (((3 / 4 - ε / 2 : ℝ) : ℂ) - ((t / 2 : ℝ) : ℂ) * Complex.I)

/-- The Bessel correction from the packet's repair context. -/
noncomputable def besselCorrection (ε t : ℝ) : ℝ :=
  (1 + t ^ 2) ^ (-5 / 8 + ε / 4)

/-- The exact frame weight from the packet's repair context. -/
noncomputable def frameWeight (ε t : ℝ) : ℝ :=
  2 * Real.cosh (Real.pi * t / 2) *
      (1 + t ^ 2) ^ (-5 / 4 + ε / 2) * ‖frameMultiplier ε t‖ ^ 2

/-- Frame weight is positive, has the stated two-sided limit, and is globally bounded above and below. -/
def frameWeightBoundedAboveBelow : Prop :=
  ∀ ε : ℝ, 0 ≤ ε → ε < 1 / 2 →
    (∀ t : ℝ, 0 < frameWeight ε t) ∧
    Filter.Tendsto (frameWeight ε) (Filter.cocompact ℝ)
      (nhds (Real.pi * 2 ^ (ε - 3 / 2))) ∧
    ∃ c C : ℝ,
      0 < c ∧ c ≤ C ∧
      ∀ t : ℝ, c ≤ frameWeight ε t ∧ frameWeight ε t ≤ C

end MathlibPlus.Open.Analysis
