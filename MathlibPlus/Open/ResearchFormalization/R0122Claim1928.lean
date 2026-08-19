import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0122Claim1928

noncomputable section

private def classicalBoundary (denominator height : ℝ) : ℝ :=
  1 - 1 / (denominator * Real.log height)

private def classicalRegion (denominator height : ℝ) : Set ℝ :=
  {sigma : ℝ | classicalBoundary denominator height < sigma}

/-- Claim 1928: the exact denominator gaps and the strict widening of the
associated classical zero-free half-planes at every height in the stated
range.  The zeta nonvanishing theorem and its certified source packet are not
reconstructed by this comparison declaration. -/
def recordComparisonInequalities_claim1928 : Prop :=
  (((4.82 : ℝ) - 4.81 = 1 / 100) ∧
      (0 : ℝ) < 4.82 - 4.81) ∧
    (((4.862 : ℝ) - 4.81 = 13 / 250) ∧
      (0 : ℝ) < 4.862 - 4.81) ∧
    (∀ height : ℝ, 2 ≤ height →
      classicalRegion 4.81 height ⊃ classicalRegion 4.82 height ∧
      classicalRegion 4.81 height ⊃ classicalRegion 4.862 height)

end

end MathlibPlus.Open.ResearchFormalization.R0122Claim1928
