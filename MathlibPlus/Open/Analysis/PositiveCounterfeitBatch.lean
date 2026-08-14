import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.Analysis

def positiveEulerNumerator (u : ℂ) : ℂ := 1 + 7 * u + 9 * u ^ 2

def positiveEulerModel (u : ℂ) : ℂ :=
  positiveEulerNumerator u / ((1 - u) * (1 - 9 * u))

def positiveEulerAlpha : ℝ := (-7 - Real.sqrt 13) / 2

def positiveEulerBeta : ℝ := (-7 + Real.sqrt 13) / 2

def positiveEulerPointCount (r : ℕ) : ℝ :=
  1 + (9 : ℝ) ^ r - positiveEulerAlpha ^ r - positiveEulerBeta ^ r

def positiveEulerExponent (m : ℕ) : ℝ :=
  if m = 0 then 0 else
    (∑ d ∈ Nat.divisors m,
      (ArithmeticFunction.moebius d : ℝ) * positiveEulerPointCount (m / d)) /
      (m : ℝ)

def positiveEulerDenominator (C L : ℝ) (z : ℂ) : ℂ :=
  (C : ℂ) + Complex.cosh ((L : ℂ) * z)

def positiveEulerReciprocal (C L : ℝ) (z : ℂ) : ℂ :=
  (positiveEulerDenominator C L z)⁻¹

def positiveEulerPole (C L : ℝ) (z : ℂ) : Prop :=
  MeromorphicAt (positiveEulerReciprocal C L) z ∧
    ¬AnalyticAt ℂ (positiveEulerReciprocal C L) z

def positiveEulerArgument (s : ℂ) : ℂ :=
  Complex.exp (-s * (Real.log 9 : ℂ))

def positiveEulerZeroLine (σ : ℝ) : Set ℂ :=
  {s | s.re = σ ∧
    ∃ k : ℤ, s.im = (2 * (k : ℝ) + 1) * Real.pi / Real.log 9}

def positiveEulerLeftAbscissa : ℝ :=
  Real.log |(-7 + Real.sqrt 13) / 2| / Real.log 9

def positiveEulerRightAbscissa : ℝ :=
  Real.log |(-7 - Real.sqrt 13) / 2| / Real.log 9

/-- The positive-Euler reciprocal model has positive integral point counts
and Euler exponents, while its numerator gives one zero line on each side of
`Re(s) = 1/2`. -/
def claim_9500 : Prop :=
  (∀ r : ℕ, 0 < r →
      ∃ q : ℕ, 0 < q ∧ positiveEulerPointCount r = (q : ℝ)) ∧
  (∀ m : ℕ, 0 < m →
      ∃ q : ℕ, 0 < q ∧ positiveEulerExponent m = (q : ℝ)) ∧
  (∀ s : ℂ,
      positiveEulerNumerator (positiveEulerArgument s) = 0 ↔
        s ∈ positiveEulerZeroLine positiveEulerLeftAbscissa ∨
        s ∈ positiveEulerZeroLine positiveEulerRightAbscissa) ∧
  positiveEulerLeftAbscissa < 1 / 2 ∧
  1 / 2 < positiveEulerRightAbscissa

/-- The explicit positive-boundary reciprocal counterfeit, including its
involution and boundary-positivity preservation properties. -/
def claim_9332 : Prop :=
  ∀ C L : ℝ, 1 < C → 0 < L →
    let D := positiveEulerDenominator C L
    (∀ z : ℂ, D (-z) = D z) ∧
    (∀ z : ℂ, D (star z) = star (D z)) ∧
    (∀ t : ℝ,
      D ((t : ℂ) * Complex.I) = (C + Real.cos (L * t) : ℂ) ∧
      C - 1 ≤ C + Real.cos (L * t)) ∧
    (∀ k : ℤ,
      positiveEulerPole C L
        ((((Real.arcosh C : ℝ) : ℂ) +
            (((2 * (k : ℝ) + 1) * Real.pi : ℝ) : ℂ) * Complex.I) /
          (L : ℂ))) ∧
    (∀ k : ℤ,
      positiveEulerPole C L
        ((-((Real.arcosh C : ℝ) : ℂ) +
            (((2 * (k : ℝ) + 1) * Real.pi : ℝ) : ℂ) * Complex.I) /
          (L : ℂ))) ∧
    (∃ z : ℂ, positiveEulerPole C L z ∧ 0 < z.re) ∧
    (∀ A N : ℂ → ℂ,
      (∀ z : ℂ, A z * A (-z) = 1) →
      (∀ z : ℂ, N z = A z * N (-z)) →
      (∀ t : ℝ, (N ((t : ℂ) * Complex.I)).im = 0 ∧
        0 < (N ((t : ℂ) * Complex.I)).re) →
      (∀ z : ℂ,
        (N z / D z) = A z * (N (-z) / D (-z))) ∧
      (∀ t : ℝ,
        (N ((t : ℂ) * Complex.I) / D ((t : ℂ) * Complex.I)).im = 0 ∧
        0 < (N ((t : ℂ) * Complex.I) / D ((t : ℂ) * Complex.I)).re))

end MathlibPlus.Open.Analysis
