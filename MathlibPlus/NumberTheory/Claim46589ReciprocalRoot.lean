import Mathlib

namespace MathlibPlus.NumberTheory.Claim46589

/--
The reciprocal-root algebraic core of claim 46589.  If `α` is a nonzero root
of the reciprocal quadratic `X^2 - A X + 1`, then its reciprocal-pair distance
satisfies `(α - α⁻¹)^2 = A^2 - 4`.  The packet's CRT witness and selected-prime
valuation conditions are not defined here and are therefore not silently
invented.
-/
theorem reciprocalRootDistanceSquare_claim46589 (A α : ℚ) (hα : α ≠ 0)
    (hroot : α ^ 2 - A * α + 1 = 0) :
    (α - α⁻¹) ^ 2 = A ^ 2 - 4 := by
  field_simp [hα]
  nlinarith [hroot]

end MathlibPlus.NumberTheory.Claim46589
