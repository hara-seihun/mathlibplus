import Mathlib

namespace MathlibPlus.Open.Research.K0163

open scoped BigOperators

noncomputable section

/-- The divisor-sum quotient used in Robin's function. -/
def sigmaReal (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (d : ℝ)

def robinQuotient (n : ℕ) : ℝ :=
  sigmaReal n / ((n : ℝ) * Real.log (Real.log (n : ℝ)))

def primePowerSum (p k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, (p : ℝ) ^ (j + 1)

/-- The exponent breakpoint and its logarithmic integral coordinate. -/
def breakpointF (p k : ℕ) : ℝ :=
  (Real.log (p : ℝ))⁻¹ *
    Real.log (1 + (primePowerSum p k)⁻¹)

def eta (p : ℕ) (y : ℝ) : ℝ :=
  (Real.log (p : ℝ))⁻¹ *
    Real.log (Real.log (y + Real.log (p : ℝ)) / Real.log y)

def etaIntegral (p : ℕ) (y : ℝ) : ℝ :=
  (Real.log (p : ℝ))⁻¹ *
    (∫ v in y..y + Real.log (p : ℝ), 1 / (v * Real.log v))

def primeValuation (p n : ℕ) : ℕ := n.factorization p

def omega (n : ℕ) : ℕ :=
  n.factorization.sum (fun _ e => e)

/-- The logarithmic integral identity included in the breakpoint-coordinate
packet. -/
def claim9720 : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (y : ℝ), 1 < y →
    eta p y = etaIntegral p y

/-- A concrete two-sided one-prime local maximum predicate for `G`. -/
def twoSidedOnePrimeLocalMaximum (n : ℕ) : Prop :=
  0 < n ∧ 1 < Real.log (n : ℝ) ∧
    (∀ p : ℕ, p.Prime →
      robinQuotient (n * p) ≤ robinQuotient n) ∧
    (∀ p : ℕ, p.Prime → p ∣ n →
      robinQuotient (n / p) ≤ robinQuotient n)

def epsilonAt (n : ℕ) : ℝ :=
  (Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)))⁻¹

/-- Exact increment on multiplying by a prime. -/
def claim9721 : Prop :=
  ∀ (p n : ℕ), p.Prime → 0 < n → 1 < Real.log (n : ℝ) →
    Real.log (robinQuotient (n * p)) - Real.log (robinQuotient n) =
      Real.log (p : ℝ) *
        (breakpointF p (primeValuation p n + 1) - eta p (Real.log (n : ℝ)))

/-- Exact increment on removing a prime factor. -/
def claim9722 : Prop :=
  ∀ (p n : ℕ), p.Prime → p ∣ n → 1 ≤ primeValuation p n →
    Real.exp 1 < (n / p : ℝ) →
    Real.log (robinQuotient n) - Real.log (robinQuotient (n / p)) =
      Real.log (p : ℝ) *
        (breakpointF p (primeValuation p n) -
          eta p (Real.log (n : ℝ) - Real.log (p : ℝ)))

/-- Prime-neighbor maximality yields every adjacent breakpoint inequality. -/
def claim9725 : Prop :=
  ∀ (n : ℕ), 3 ≤ omega n → twoSidedOnePrimeLocalMaximum n →
    (∀ (p : ℕ), p.Prime → p ∣ n →
      breakpointF p (primeValuation p n + 1) < epsilonAt n ∧
        epsilonAt n < breakpointF p (primeValuation p n)) ∧
    (∀ (p : ℕ), p.Prime → ¬ p ∣ n →
      breakpointF p 1 < epsilonAt n)

end

end MathlibPlus.Open.Research.K0163
