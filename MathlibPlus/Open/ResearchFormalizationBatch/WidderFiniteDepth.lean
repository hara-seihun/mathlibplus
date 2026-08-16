import Mathlib

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-! Claim 11291: the finite-depth Widder counterexample. -/

def widderCounterfeitPolynomial (M : ℕ) (a b : ℝ) (z : ℂ) : ℂ :=
  (z ^ 2 + (a : ℂ)) ^ M * ((z ^ 2 + (a : ℂ)) ^ 2 + (b : ℂ) ^ 2)

def shiftedWidderDensity (M : ℕ) (a b t : ℝ) : ℝ :=
  Real.exp (-(a + (1 / 4 : ℝ)) * t) *
    (2 * (M : ℝ) + 4 * Real.cos (b * t))

def shiftedDescendedLogDerivative (M : ℕ) (a b y : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-y * t) * shiftedWidderDensity M a b t

def widderFunction (h : ℝ → ℝ) (k : ℕ) : ℝ → ℝ :=
  fun y => iteratedDeriv k (fun x => x ^ k * h x) y

def completelyMonotoneOnPositive (f : ℝ → ℝ) : Prop :=
  ∀ (m : ℕ) (y : ℝ), 0 < y →
    0 ≤ (-1 : ℝ) ^ m * iteratedDeriv m f y

def hasOffAxisQuartet (M : ℕ) (a b : ℝ) : Prop :=
  ∃ z : ℂ,
    z ^ 2 = -(a : ℂ) + Complex.I * (b : ℂ) ∧
      z.re ≠ 0 ∧ z.im ≠ 0 ∧
      widderCounterfeitPolynomial M a b z = 0 ∧
      widderCounterfeitPolynomial M a b (-z) = 0 ∧
      widderCounterfeitPolynomial M a b (starRingEnd ℂ z) = 0 ∧
      widderCounterfeitPolynomial M a b (-starRingEnd ℂ z) = 0 ∧
      z ≠ -z ∧ z ≠ starRingEnd ℂ z ∧ z ≠ -starRingEnd ℂ z ∧
      -z ≠ starRingEnd ℂ z ∧ -z ≠ -starRingEnd ℂ z ∧
        starRingEnd ℂ z ≠ -starRingEnd ℂ z

def finiteWidderDepthOutcome (N M : ℕ) (a b : ℝ) : Prop :=
  (∀ k : ℕ, 0 ≤ k → k ≤ N →
      completelyMonotoneOnPositive
        (widderFunction (shiftedDescendedLogDerivative M a b) k)) ∧
    hasOffAxisQuartet M a b

def finiteWidderDepthCanBeFooled : Prop :=
  (∀ (N M : ℕ) (a b : ℝ),
    0 < M → 0 < a → 0 < b →
      (M : ℝ) ≥
          2 * Real.rpow
            (1 + b ^ 2 / (a + (1 / 4 : ℝ)) ^ 2)
            ((N : ℝ) / 2) →
        finiteWidderDepthOutcome N M a b) ∧
    (∀ N : ℕ, ∃ (M : ℕ) (a b : ℝ),
      0 < M ∧ 0 < a ∧ 0 < b ∧
        (M : ℝ) ≥
          2 * Real.rpow
            (1 + b ^ 2 / (a + (1 / 4 : ℝ)) ^ 2)
            ((N : ℝ) / 2) ∧
        finiteWidderDepthOutcome N M a b)

end MathlibPlus.Open.ResearchFormalizationBatch
