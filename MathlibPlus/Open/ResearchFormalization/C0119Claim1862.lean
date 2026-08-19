import Mathlib
import MathlibPlus.Open.ResearchFormalization.C0102C0119Batch
import MathlibPlus.Open.Research.AdmittedBatch1861

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.C0119Claim1862

open MathlibPlus.Open.ResearchFormalization.C0102C0119
open MathlibPlus.Open.Research

noncomputable section

/-- Evaluation of a rational polynomial in the half-shift variable. -/
def rationalPolynomialEvaluation1862 (p : Polynomial ℚ) (b : ℝ) : ℝ :=
  Polynomial.eval₂ (algebraMap ℚ ℝ) b p

/-- The exact half-shifted near-hook minor and principal minor carriers. -/
def nearHookNumerator1862 (d n ell : ℕ) (b : ℝ) : ℝ :=
  rationalPolynomialEvaluation1862 (nearHookPoly d n ell) b

def principalDenominator1862 (d : ℕ) (b : ℝ) : ℝ :=
  rationalPolynomialEvaluation1862 (principalPoly d) b

/-- The shifted variable and the rising-factorial form of `Delta`. -/
def y1862 (d : ℕ) (b : ℝ) : ℝ :=
  2 * b + (d : ℝ) + 1

def rising1862 (x : ℝ) (k : ℕ) : ℝ :=
  ∏ r ∈ Finset.range k, (x + (r : ℝ))

def delta1862 (d n ell : ℕ) (b : ℝ) : ℝ :=
  y1862 d b * rising1862
    (y1862 d b - ((ell + 1 : ℕ) : ℝ)) (n + ell + 1)

/-- The pure near-hook determinant and the exact normalized numerator `X`. -/
def pureNearHookValue1862 (d n ell : ℕ) : ℝ :=
  (pureNearHookDeterminant n ell (d - ell - 1) : ℝ)

def x1862 (d n ell : ℕ) : ℝ :=
  (((d : ℝ) + 1) * ((d : ℝ) + (n : ℝ))) /
      (((d - ell - 1 : ℕ) : ℝ) * (d : ℝ)) *
    pureNearHookValue1862 d n ell

/-- Claim 1862: the normalized near-hook minor identity with the exact
principal, Riordan-tail, shifted-variable, and rising-factorial carriers. -/
def claim1862 : Prop :=
  ∀ (b : ℝ) (d n ell : ℕ),
    2 ≤ n → 1 ≤ ell → max n (ell + 2) ≤ d →
      nearHookNumerator1862 d n ell b /
          principalDenominator1862 d b =
        x1862 d n ell /
          delta1862 d n ell b

end

end MathlibPlus.Open.ResearchFormalization.C0119Claim1862
