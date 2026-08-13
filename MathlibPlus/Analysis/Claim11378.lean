import Mathlib

namespace MathlibPlus.Analysis.Claim11378

/-- The two polarized root-cone expressions in claim 11378, with the source's
real and imaginary coordinates made explicit. -/
noncomputable def polarizedA6 (xAlpha aAlpha xBeta aBeta : ℝ) : ℝ :=
  ((aAlpha - aBeta) ^ 2 + 4 * xAlpha * xBeta) / 4

noncomputable def polarizedK6 (xAlpha aAlpha xBeta aBeta : ℝ) : ℝ :=
  ((aAlpha - aBeta) ^ 2 + xAlpha ^ 2 + 6 * xAlpha * xBeta + xBeta ^ 2) / 4

/-- The exact two forms and their sharp difference identity. -/
theorem polarizedRootConeDifference_claim11378
    (xAlpha aAlpha xBeta aBeta : ℝ) :
    4 * polarizedA6 xAlpha aAlpha xBeta aBeta =
        (aAlpha - aBeta) ^ 2 + 4 * xAlpha * xBeta ∧
      4 * polarizedK6 xAlpha aAlpha xBeta aBeta =
        (aAlpha - aBeta) ^ 2 + xAlpha ^ 2 + 6 * xAlpha * xBeta + xBeta ^ 2 ∧
      4 * (polarizedK6 xAlpha aAlpha xBeta aBeta -
        polarizedA6 xAlpha aAlpha xBeta aBeta) = (xAlpha + xBeta) ^ 2 := by
  dsimp [polarizedA6, polarizedK6]
  constructor
  · ring
  constructor
  · ring
  · ring

end MathlibPlus.Analysis.Claim11378
