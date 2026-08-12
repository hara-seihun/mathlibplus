import MathlibPlus.Algebra.LinearQuadraticFactorization

namespace MathlibPlus.NumberTheory.Claim20344

/-- The degree inequality in claim 20344, with the scalar convention made
explicit over the rationals. -/
theorem minimalSalemFactorLowerBound_claim20344 {N C D : ℚ}
    (hD : D = N - C) (hC : C ≤ 5 * N / 6) :
    N / 6 ≤ D := by
  linarith

end MathlibPlus.NumberTheory.Claim20344
