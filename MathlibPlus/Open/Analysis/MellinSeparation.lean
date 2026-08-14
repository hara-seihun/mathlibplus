import Mathlib

open MeasureTheory

noncomputable section

namespace MathlibPlus.Open.Analysis

/-- The zero extension of a compactly supported smooth function on the positive reals. -/
def MellinTestFunction :=
  {f : ℝ → ℂ //
    ContDiff ℝ ⊤ f ∧
      IsCompact (tsupport f) ∧
      tsupport f ⊆ Set.Ioi (0 : ℝ)}

/-- The convention `∫₀^∞ f(x) x^s dx/x` on the test-function carrier. -/
def mellinTransform (f : MellinTestFunction) (s : ℂ) : ℂ :=
  ∫ x : ℝ in Set.Ioi (0 : ℝ), f.1 x * Complex.cpow (x : ℂ) s / (x : ℂ)

/-- Every prescribed complex function on a finite packet of root values is
realized by one Mellin transform. -/
def mellinSeparationOnFiniteZeroPacket (roots : Finset ℂ) : Prop :=
  ∀ prescribed : roots → ℂ,
    ∃ f : MellinTestFunction,
      ∀ root : roots, mellinTransform f root = prescribed root

end MathlibPlus.Open.Analysis
