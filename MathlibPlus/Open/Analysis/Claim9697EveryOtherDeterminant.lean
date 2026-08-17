import MathlibPlus.Open.Analysis.ReflectedAllRankCoefficientPositivity

namespace MathlibPlus.Open.Analysis.Claim9697

open Polynomial
open MathlibPlus.Open.Analysis

/-- Claim 9697: the every-other determinant is divisible by the stated
monomial, and the canonical quotient is the integral normalized polynomial. -/
def everyOtherDeterminant_normalizedPolynomial_claim9697 : Prop :=
  ∀ r : Nat,
    X ^ (Nat.choose r 2) ∣ everyOtherDeterminant r ∧
      everyOtherDeterminant r =
        X ^ (Nat.choose r 2) * normalizedPolynomial r ∧
      HasIntegralCoefficients (normalizedPolynomial r)

end MathlibPlus.Open.Analysis.Claim9697
