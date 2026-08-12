import MathlibPlus.Basic

namespace MathlibPlus.Arithmetic

/-- Exact rational arithmetic recorded in claim 56574. -/
theorem baseBoundQuadraticTail_claim56574 :
    (1579 / 10000 : ℚ) + (1 / 2) * (1 / 10)^2 = 1629 / 10000 := by
  norm_num

end MathlibPlus.Arithmetic
