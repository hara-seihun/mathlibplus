import Mathlib

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.NumberTheory

/-- The primes not exceeding a natural-number cutoff. -/
def primesAtMost (y : ℕ) : Finset ℕ :=
  (Finset.Iic y).filter Nat.Prime

/-- The primorial attached to a cutoff. -/
def primorial (y : ℕ) : ℕ :=
  ∏ p ∈ primesAtMost y, p

/-- The number of primes not exceeding the cutoff. -/
def primeCount (y : ℕ) : ℕ :=
  Nat.primeCounting y

/-- The Möbius function, viewed as real-valued for the analytic expressions. -/
def realMoebius (n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius n : ℝ)

/-- The linear-port subtraction used in the claim. -/
def linearPort (x : ℝ) : ℝ :=
  Real.exp (-x) - 1 + x

/-- The primorial Euler factor at exponent one. -/
def primorialEulerFactor (y : ℕ) : ℝ :=
  ∏ p ∈ primesAtMost y, (1 - (1 : ℝ) / p)

/-- The finite Möbius dilation sum. -/
def finiteMoebiusDilation (y : ℕ) (t : ℝ) : ℝ :=
  ∑ d ∈ Nat.divisors (primorial y),
    realMoebius d * Real.exp (-((d : ℝ) * t))

/-- The canonical linear-port remainder. -/
def canonicalRemainder (y : ℕ) (x : ℝ) : ℝ :=
  ((-1 : ℝ) ^ primeCount y) *
      finiteMoebiusDilation y (x / (primorial y : ℝ)) +
    x * primorialEulerFactor y

/-- The Euler product occurring in the Taylor coefficients. -/
def TaylorEulerFactor (y k : ℕ) : ℝ :=
  ∏ p ∈ primesAtMost y, (1 - ((p : ℝ)⁻¹) ^ k)

/-- The displayed Taylor series, with the summation convention `k ≥ 2`. -/
def canonicalTaylorSeries (y : ℕ) (x : ℝ) : ℝ :=
  ∑' k : ℕ,
    if 2 ≤ k then
      ((-x) ^ k / (Nat.factorial k : ℝ)) * TaylorEulerFactor y k
    else
      0

/--
Canonical linear-port subtraction: the Möbius cancellation identities define the
remainder and its entire Taylor series.
-/
def canonicalLinearPortSubtraction : Prop :=
  ∀ y : ℕ,
    (∑ e ∈ Nat.divisors (primorial y), realMoebius e = 0) ∧
    (∑ e ∈ Nat.divisors (primorial y),
        realMoebius e / (e : ℝ) = primorialEulerFactor y) ∧
    (∀ x : ℝ,
      canonicalRemainder y x =
          ∑ e ∈ Nat.divisors (primorial y),
            realMoebius e * linearPort (x / (e : ℝ))) ∧
    (∀ x : ℝ,
      canonicalRemainder y x = canonicalTaylorSeries y x)

end MathlibPlus.Open.NumberTheory
