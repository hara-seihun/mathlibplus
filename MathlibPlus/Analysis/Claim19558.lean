import Mathlib

namespace MathlibPlus.Analysis.R0302

/-- The second nontrivial root in the exact first-square-gap witness. -/
noncomputable def secondRoot19558 : ℝ :=
  (25 + Real.sqrt 569) / 8

/-- The source polynomial whose second root is below the second square barrier. -/
noncomputable def witnessPolynomial19558 (q : ℝ) : ℝ :=
  (q - 2) * (8 * q ^ 2 - 50 * q + 7) / 2

/-- Claim 19558: the second root lies strictly between 2 and the barrier 8. -/
def secondSquareBarrierNotCrossed_claim19558 : Prop :=
  witnessPolynomial19558 (secondRoot19558) = 0 ∧
    2 < secondRoot19558 ∧
    secondRoot19558 < 8

end MathlibPlus.Analysis.R0302
