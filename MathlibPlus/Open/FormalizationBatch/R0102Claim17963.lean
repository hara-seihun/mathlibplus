import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.R0102Claim17963

noncomputable section

/-- The center coordinate from the two-particle logarithmic chart. -/
private def centerCoordinate (u v : ℝ) : ℝ :=
  (u + v) / 2

/-- The relative coordinate from the two-particle logarithmic chart. -/
private def relativeCoordinate (u v : ℝ) : ℝ :=
  (u - v) / 2

/-- The shifted relative coordinate for positive shell indices. -/
private def shiftedRelativeCoordinate (m n : ℕ) (u v : ℝ) : ℝ :=
  relativeCoordinate u v +
    (1 / 2 : ℝ) * Real.log ((m : ℝ) / (n : ℝ))

/-- Claim 17963: exchanging the positive shell particles fixes the center and
reverses both the relative and shifted relative coordinates. -/
def claim17963 : Prop :=
  ∀ (m n : ℕ), 0 < m → 0 < n → ∀ (u v : ℝ),
    centerCoordinate u v = centerCoordinate v u ∧
      relativeCoordinate v u = -relativeCoordinate u v ∧
      shiftedRelativeCoordinate n m v u =
        -shiftedRelativeCoordinate m n u v

end

end MathlibPlus.Open.FormalizationBatch.R0102Claim17963
