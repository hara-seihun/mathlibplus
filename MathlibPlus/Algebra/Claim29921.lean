import Mathlib
import MathlibPlus.Algebra.Claim29919

namespace MathlibPlus.Algebra.Claim29921

/-- The unreduced numerator and denominator of the midpoint completion differ by
    the displayed two-factor expression. -/
theorem numeratorMinusDenominator {K : Type*} [Field K]
    (p q : ℕ) (δ Z : K) :
    MathlibPlus.Algebra.Claim29919.numerator p q δ Z -
        MathlibPlus.Algebra.Claim29919.denominator p q δ Z =
      δ * ((p : K) - (q : K)) * (Z ^ p - 1) * (Z ^ q - 1) := by
  simp only [MathlibPlus.Algebra.Claim29919.numerator,
    MathlibPlus.Algebra.Claim29919.denominator]
  ring

end MathlibPlus.Algebra.Claim29921
