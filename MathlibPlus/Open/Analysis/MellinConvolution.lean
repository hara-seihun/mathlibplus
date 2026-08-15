import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis

abbrev PositiveReal := Set.Ioi (0 : ℝ)

/-- The zero extension to `ℝ` of a function on the positive reals. -/
def positiveLift (f : PositiveReal → ℂ) (x : ℝ) : ℂ :=
  if hx : 0 < x then f ⟨x, hx⟩ else 0

/-- Compactly supported smooth test functions on the positive reals. -/
def PositiveCompactSmooth (f : PositiveReal → ℂ) : Prop :=
  ContDiffOn ℝ ⊤ (positiveLift f) (Set.Ioi 0) ∧
    IsCompact (tsupport f)

/-- Multiplicative convolution with Haar measure `dy / y`. -/
def multiplicativeConvolution (f g : PositiveReal → ℂ) (x : PositiveReal) : ℂ :=
  ∫ y : ℝ,
    (if hy : 0 < y then
        f ⟨y, hy⟩ * g ⟨x.1 / y, div_pos x.2 hy⟩ / (y : ℂ)
      else 0) ∂(MeasureTheory.Measure.restrict MeasureTheory.MeasureSpace.volume (Set.Ioi 0))

/-- Mellin transform with the convention `∫ f(x) x^s dx / x`. -/
def mellinTransform (f : PositiveReal → ℂ) (s : ℂ) : ℂ :=
  ∫ x : ℝ,
    (if hx : 0 < x then
        f ⟨x, hx⟩ * Complex.cpow (x : ℂ) s / (x : ℂ)
      else 0) ∂(MeasureTheory.Measure.restrict MeasureTheory.MeasureSpace.volume (Set.Ioi 0))

/-- The Mellin transform turns multiplicative convolution into multiplication. -/
def mellinTransform_multiplicativeConvolution : Prop :=
  ∀ (f g : PositiveReal → ℂ),
    PositiveCompactSmooth f →
    PositiveCompactSmooth g →
    ∀ s : ℂ,
      mellinTransform (multiplicativeConvolution f g) s =
        mellinTransform f s * mellinTransform g s

end MathlibPlus.Open.Analysis
