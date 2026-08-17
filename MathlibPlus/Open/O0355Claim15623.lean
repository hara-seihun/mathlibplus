import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.O0355Claim15623

noncomputable section

abbrev MultiIndex := Fin 5 →₀ ℕ
abbrev Series := MvPowerSeries (Fin 5) ℤ

/-- The nonconstant monomials allowed by the displayed cyclotomic product. -/
def supportedIndex (n : MultiIndex) : Prop :=
  1 ≤ n 0 ∧ 1 ≤ ∑ j : Fin 4, n j.succ

def totalDegree (n : MultiIndex) : ℕ :=
  ∑ j : Fin 5, n j

def monomialSeries (n : MultiIndex) : Series :=
  MvPowerSeries.monomial n 1

def cyclotomicFactor (n : MultiIndex) : Series :=
  1 - monomialSeries n

/-- The inverse supplied by the unit-valued formal-series construction. -/
noncomputable def cyclotomicFactorInverse (n : MultiIndex) : Series :=
  MvPowerSeries.invOfUnit (cyclotomicFactor n) (1 : ℤˣ)

def integerPower (n : MultiIndex) : ℤ → Series
  | Int.ofNat k => cyclotomicFactor n ^ k
  | Int.negSucc k => cyclotomicFactorInverse n ^ (k + 1)

def finiteCyclotomicProduct
    (c : MultiIndex → ℤ) (F : Finset MultiIndex) : Series :=
  ∏ n ∈ F, integerPower n (c n)

def formalDenominator (m : ℕ) : Series :=
  let X := monomialSeries (Finsupp.single (0 : Fin 5) 1)
  let U : Fin 4 → Series := fun j =>
    monomialSeries (Finsupp.single j.succ 1)
  1 - (1 - MvPowerSeries.C (m : ℤ) * ∑ j : Fin 4, U j) * X

noncomputable def formalDenominatorInverse (m : ℕ) : Series :=
  MvPowerSeries.invOfUnit (formalDenominator m) (1 : ℤˣ)

/-- The displayed quotient, formed in the integral multivariate series ring. -/
noncomputable def integralW (m : ℕ) : Series :=
  let X := monomialSeries (Finsupp.single (0 : Fin 5) 1)
  (1 - X) * formalDenominatorInverse m

def formalCyclotomicFactorization
    (m : ℕ) (c : MultiIndex → ℤ) : Prop :=
  (formalDenominator m * formalDenominatorInverse m = 1 ∧
      formalDenominatorInverse m * formalDenominator m = 1) ∧
    (∀ n, c n ≠ 0 → supportedIndex n ∧
      (cyclotomicFactor n) * cyclotomicFactorInverse n = 1 ∧
      cyclotomicFactorInverse n * (cyclotomicFactor n) = 1) ∧
    ∀ d : MultiIndex, ∃ F : Finset MultiIndex,
      (∀ n, n ∈ F ↔ c n ≠ 0 ∧ supportedIndex n ∧
        totalDegree n ≤ totalDegree d) ∧
      MvPowerSeries.coeff d (integralW m) =
        MvPowerSeries.coeff d (finiteCyclotomicProduct c F)

/-- Claim 15623: the integral coefficientwise cyclotomic factorization with
integer exponents and the four primary coefficients. -/
def claim15623 : Prop :=
  ∀ (m : ℕ), 1 ≤ m →
    ∃ c : MultiIndex → ℤ,
      (∀ n, c n ≠ 0 → supportedIndex n) ∧
      formalCyclotomicFactorization m c ∧
      (∀ j : Fin 4,
        c (Finsupp.single (0 : Fin 5) 1 +
          Finsupp.single j.succ 1) = (m : ℤ))

end

end MathlibPlus.Open.O0355Claim15623
