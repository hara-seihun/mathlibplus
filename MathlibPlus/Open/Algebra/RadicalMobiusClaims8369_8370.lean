import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.RadicalMobiusClaims

/-- The complex power convention used by the displayed Dirichlet factors. -/
noncomputable def complexNatPower (n : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (s * Complex.log (n : ℂ))

/-- The divisor sum `σ_s(n)` for a complex exponent. -/
noncomputable def complexDivisorSigma (s : ℂ) (n : ℕ) : ℂ :=
  (Nat.divisors n).sum (fun d => complexNatPower d s)

/-- The signed outer divisor mass in Claim 8369. -/
noncomputable def signedDivisorMass (R : ℕ) (w : ℂ) : ℂ :=
  (Nat.divisors R).sum (fun h =>
    ((ArithmeticFunction.moebius h : ℤ) : ℂ) *
      complexNatPower h (-w) *
      complexDivisorSigma (-1 - w) (R / h))

/-- The local-factor product in Claim 8369. -/
noncomputable def signedEulerProduct (R : ℕ) (w : ℂ) : ℂ :=
  (R.primeFactors).prod (fun p =>
    1 + complexNatPower p (-1 - w) - complexNatPower p (-w))

/-- The signed coefficient Euler product from Claim 8369. -/
def signedCoefficientEulerProduct_claim8369 : Prop :=
  ∀ R : ℕ, 0 < R → Squarefree R →
    ∀ w : ℂ, signedDivisorMass R w = signedEulerProduct R w

/--
The exact Mellin-boundary specialization from Claim 8370.  The divisor sum is
kept as the explicit finite sum, and the result is the complex reciprocal
`1/R` rather than an informal scalar abbreviation.
-/
def exactMellinBoundarySuppression_claim8370 : Prop :=
  ∀ R : ℕ, 0 < R → Squarefree R →
    signedDivisorMass R 0 = (R : ℂ)⁻¹

end MathlibPlus.Open.RadicalMobiusClaims
