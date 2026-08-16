import Mathlib

noncomputable section

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

def counterfeitAlpha : ℝ := (-7 + Real.sqrt 13) / 2

def counterfeitBeta : ℝ := (-7 - Real.sqrt 13) / 2

def counterfeitPointCount (n : ℕ) : ℝ :=
  9 ^ n + 1 - (counterfeitAlpha ^ n + counterfeitBeta ^ n)

def counterfeitMobiusSum (n : ℕ) : ℝ :=
  (Nat.divisors n).sum (fun d =>
    (ArithmeticFunction.moebius d : ℝ) * counterfeitPointCount (n / d))

def counterfeitPolynomial : Polynomial ℚ :=
  1 + 7 * Polynomial.X + 9 * Polynomial.X ^ 2

def counterfeitNumerator : PowerSeries ℚ :=
  Polynomial.toPowerSeries counterfeitPolynomial

def counterfeitZMinus : PowerSeries ℚ :=
  counterfeitNumerator *
    ((1 - PowerSeries.X) * (1 - 9 * PowerSeries.X))⁻¹

/-- The coefficientwise finite truncation of the formal Euler product. -/
def counterfeitFormalEulerProduct (B : ℕ → ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n =>
    PowerSeries.coeff n
      ((Finset.range (n + 1)).prod (fun d =>
        ((1 - PowerSeries.X ^ (d + 1))⁻¹) ^ B (d + 1))))

def claim12791 : Prop :=
  ∃ N B : ℕ → ℕ,
    (∀ n, 0 < n →
      0 < N n ∧ (N n : ℝ) = counterfeitPointCount n) ∧
    (∀ n : ℕ, 0 < n →
      (n : ℝ) * B n = counterfeitMobiusSum n ∧ 0 < B n) ∧
    counterfeitZMinus = counterfeitFormalEulerProduct B

end MathlibPlus.Open.Analysis
