import Mathlib

namespace MathlibPlus.Open.Analysis

open MeasureTheory

/-- The anisotropic complex rectangle around the negative real saddle. -/
def anisotropicSaddleNeighborhood (R : ℝ) : Set ℂ :=
  {z | ∃ u v : ℝ,
    z = (-R : ℂ) + (u : ℂ) + (v : ℂ) * Complex.I ∧
      |u| ≤ 1 / (16 * R) ∧ |v| ≤ 1 / 4}

/-- For all sufficiently large positive `R`, the displayed saddle
neighborhood has area `1/(16 R)`. -/
def anisotropicSaddleNeighborhoodArea : Prop :=
  ∃ R₀ : ℝ, 0 < R₀ ∧
    ∀ R : ℝ, R₀ ≤ R →
      volume (anisotropicSaddleNeighborhood R) =
        ENNReal.ofReal (1 / (16 * R))

end MathlibPlus.Open.Analysis
