import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

noncomputable section

open scoped BigOperators

abbrev PrimeIndex := {p : ℕ // p.Prime}

structure ArakelovQDivisor where
  finite : Finsupp PrimeIndex ℤ
  infinity : ℝ

def ArakelovQDegreeZero (D : ArakelovQDivisor) : Prop :=
  D.infinity = -∑ p ∈ D.finite.support, (D.finite p : ℝ) * Real.log (p : ℝ)

def primeUnit (p : PrimeIndex) : ℚˣ :=
  Units.mk0 (p : ℚ) (by exact_mod_cast p.property.ne_zero)

def primeProductUnit (n : Finsupp PrimeIndex ℤ) : ℚˣ :=
  ∏ p ∈ n.support, (primeUnit p) ^ (n p)

def IsPrincipalArakelovQDivisor (D : ArakelovQDivisor) (q : ℚˣ) : Prop :=
  (∀ p : PrimeIndex,
      D.finite p = padicValRat (p : ℕ) (q : ℚ)) ∧
    D.infinity = -Real.log |(q : ℚ)|

/-- Claim 12197, with finite-support prime coefficients and the classical principal divisor. -/
def claim12197 : Prop :=
  ∀ D : ArakelovQDivisor, ArakelovQDegreeZero D →
    IsPrincipalArakelovQDivisor D (primeProductUnit D.finite) ∧
      (∃ q : ℚˣ, IsPrincipalArakelovQDivisor D q)

end

end MathlibPlus.Open.FormalizationBatch
