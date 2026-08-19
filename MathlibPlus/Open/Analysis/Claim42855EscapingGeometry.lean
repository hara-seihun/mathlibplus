import Mathlib

namespace MathlibPlus.Open.Analysis.Claim42855

/-- The two displayed points on the imaginary axis. -/
def escapingPointPlus (R : ℝ) : ℂ := Complex.I * (R : ℂ)
def escapingPointMinus (R : ℝ) : ℂ := -Complex.I * (R : ℂ)

/-- Exact geometry of the escaping zero pair. -/
def claim42855_escapingZeroGeometry : Prop :=
  ∀ R : ℝ,
    (escapingPointPlus R).im = R ∧
    (escapingPointMinus R).im = -R ∧
    ‖escapingPointPlus R‖ = |R| ∧
    ‖escapingPointMinus R‖ = |R|

end MathlibPlus.Open.Analysis.Claim42855
