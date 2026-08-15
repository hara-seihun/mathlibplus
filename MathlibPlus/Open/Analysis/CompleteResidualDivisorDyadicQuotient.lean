import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- The zero string in the residual dyadic quotient. -/
def dyadicZeroPoint (n : ℤ) : ℂ :=
  ((1 / 2 : ℝ) : ℂ) +
    (((2 * Real.pi * (n : ℝ) / Real.log 2 : ℝ) : ℂ) * Complex.I)

/-- The two pole strings in the residual dyadic quotient. -/
def dyadicPolePlus (t : ℝ) (n : ℤ) : ℂ :=
  (((1 / 2 + t / Real.log 2 : ℝ) : ℂ)) +
    (((2 * Real.pi * (n : ℝ) / Real.log 2 : ℝ) : ℂ) * Complex.I)

def dyadicPoleMinus (t : ℝ) (n : ℤ) : ℂ :=
  (((1 / 2 - t / Real.log 2 : ℝ) : ℂ)) +
    (((2 * Real.pi * (n : ℝ) / Real.log 2 : ℝ) : ℂ) * Complex.I)

/-- The numerator of the completed residual dyadic quotient. -/
def dyadicNumerator (s : ℂ) : ℂ :=
  (Complex.cosh ((Real.log 2 : ℂ) * (s - (1 / 2 : ℂ))) - 1) ^ 6

/-- The denominator of the completed residual dyadic quotient. -/
def dyadicDenominator (t : ℝ) (s : ℂ) : ℂ :=
  (Complex.cosh ((Real.log 2 : ℂ) * (s - (1 / 2 : ℂ))) - (Real.cosh t : ℂ)) ^ 6

/-- The quotient on its regular locus, with the displayed quotient formula. -/
def dyadicQuotient (t : ℝ) (s : ℂ) : ℂ :=
  ((Complex.cosh ((Real.log 2 : ℂ) * (s - (1 / 2 : ℂ))) - 1) /
      (Complex.cosh ((Real.log 2 : ℂ) * (s - (1 / 2 : ℂ))) -
        (Real.cosh t : ℂ))) ^ 6

/-- Exact vanishing order, expressed by analyticity and the first nonzero derivative. -/
def exactComplexZeroOrder (f : ℂ → ℂ) (a : ℂ) (order : ℕ) : Prop :=
  AnalyticAt ℂ f a ∧
    (∀ k : ℕ, k < order → iteratedDeriv k f a = 0) ∧
      iteratedDeriv order f a ≠ 0

/-- A pole order for the displayed quotient is the exact denominator order
    together with nonvanishing of the numerator. -/
def exactDyadicPoleOrder (t : ℝ) (a : ℂ) (order : ℕ) : Prop :=
  dyadicNumerator a ≠ 0 ∧
    exactComplexZeroOrder (dyadicDenominator t) a order

/-- Complete residual divisor of the dyadic quotient. -/
def completeResidualDivisorDyadicQuotient : Prop :=
  ∃ t : ℝ,
    Real.cosh t = 1 + 1 / (12 * Real.sqrt 2) ∧
      0 < t ∧
        t < Real.log 2 / 2 ∧
          (∀ s : ℂ,
            (dyadicQuotient t s = 0 ∧ dyadicDenominator t s ≠ 0) ↔
              ∃ n : ℤ, s = dyadicZeroPoint n) ∧
            (∀ n : ℤ,
              exactComplexZeroOrder (dyadicQuotient t) (dyadicZeroPoint n) 12) ∧
              (∀ s : ℂ,
                (dyadicDenominator t s = 0 ∧ dyadicNumerator s ≠ 0) ↔
                  (∃ n : ℤ, s = dyadicPolePlus t n) ∨
                    (∃ n : ℤ, s = dyadicPoleMinus t n)) ∧
                (∀ n : ℤ,
                  exactDyadicPoleOrder t (dyadicPolePlus t n) 6 ∧
                    exactDyadicPoleOrder t (dyadicPoleMinus t n) 6) ∧
                  (∀ n : ℤ,
                    0 < (dyadicPolePlus t n).re ∧
                      (dyadicPolePlus t n).re < 1 ∧
                        (dyadicPolePlus t n).re ≠ (1 / 2 : ℝ) ∧
                          0 < (dyadicPoleMinus t n).re ∧
                            (dyadicPoleMinus t n).re < 1 ∧
                              (dyadicPoleMinus t n).re ≠ (1 / 2 : ℝ)) ∧
                    DifferentiableOn ℂ (dyadicQuotient t) {s : ℂ | 1 < s.re} ∧
                      (∀ s : ℂ, 1 < s.re → dyadicQuotient t s ≠ 0)

end

end MathlibPlus.Open.Analysis
