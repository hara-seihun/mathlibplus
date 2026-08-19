import Mathlib
import MathlibPlus.Open.PrimeCyclotomic.Witnesses

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.PrimeCyclotomic.PrimeCyclotomicTracePolynomialClaim12097

/-- Claim 12097: for every odd prime, the reciprocal cyclotomic identity has
one unique monic integer trace polynomial, whose explicit coefficients are the
trace-Chebyshev polynomials. -/
def primeCyclotomicTracePolynomial_claim12097 : Prop :=
  ∀ p : ℕ, Nat.Prime p → p % 2 = 1 →
    let n := (p - 1) / 2
    Polynomial.Monic (primeTracePolynomial p) ∧
      (primeTracePolynomial p =
        1 + (∑ k ∈ Finset.Icc 1 n, traceChebyshev k)) ∧
      reciprocalTraceIdentity p (primeTracePolynomial p) ∧
      (∀ q : Polynomial ℤ,
        Polynomial.Monic q →
          reciprocalTraceIdentity p q → q = primeTracePolynomial p) ∧
      (∀ k : ℕ, ∀ x : ℂ, x ≠ 0 →
        Polynomial.eval₂ (Int.castRingHom ℂ) (x + x⁻¹) (traceChebyshev k) =
          x ^ k + (x⁻¹) ^ k)

end MathlibPlus.Open.PrimeCyclotomic.PrimeCyclotomicTracePolynomialClaim12097
