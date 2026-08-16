import Mathlib

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386

/-- The explicit denominator family in the finite-depth counterexample. -/
def yM (M : ℕ) (z : ℂ) : ℂ :=
  (1 / 4 : ℂ) * (1 + z ^ 2) ^ M * (z ^ 4 + 4) *
    Complex.cosh ((Real.pi : ℂ) * z / 2)

/-- The Levy numerator attached to the denominator family. -/
def kM (M : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-x) * ((M : ℝ) + 2 * Real.cos x) +
    1 / (2 * Real.sinh x)

/-- Complete monotonicity on the positive half-line, with ordinary signed
iterated derivatives. -/
def completelyMonotoneOnPositive (f : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, ∀ x : ℝ, 0 < x →
    0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n f x

/-- A characteristic function represented by its probability measure. -/
def isCharacteristicFunction (φ : ℝ → ℂ) : Prop :=
  ∃ μ : Measure ℝ,
    IsProbabilityMeasure μ ∧
      ∀ t : ℝ,
        φ t = ∫ x : ℝ,
          Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) ∂μ

/-- Infinite divisibility on the characteristic-function carrier. -/
def isInfinitelyDivisibleCharacteristic (φ : ℝ → ℂ) : Prop :=
  isCharacteristicFunction φ ∧
    ∀ n : ℕ, 0 < n →
      ∃ ψ : ℝ → ℂ,
        isCharacteristicFunction ψ ∧
          ∀ t : ℝ, φ t = (ψ t) ^ n

/-- Symmetric self-decomposability, including the characteristic and
infinitely-divisible law premises for every residual factor. -/
def isSymmetricSelfDecomposable (φ : ℝ → ℂ) : Prop :=
  isInfinitelyDivisibleCharacteristic φ ∧
    (∀ t : ℝ, φ (-t) = φ t) ∧
    ∀ c : ℝ, 0 < c → c < 1 →
      ∃ ψ : ℝ → ℂ,
        isInfinitelyDivisibleCharacteristic ψ ∧
          ∀ t : ℝ, φ t = φ (c * t) * ψ t

/-- The four retained off-axis zeros of the unchanged quartic factor. -/
def retainsOffAxisQuartet (Y : ℂ → ℂ) : Prop :=
  Y (1 + Complex.I) = 0 ∧
    Y (1 - Complex.I) = 0 ∧
    Y (-1 + Complex.I) = 0 ∧
    Y (-1 - Complex.I) = 0

/-- Every finite signed-derivative depth can be passed by a sufficiently
large member of the explicit family, while its reciprocal remains a
symmetric self-decomposable infinitely-divisible characteristic function and
the off-axis quartet remains present. -/
def claim15355 : Prop :=
  ∀ M : ℕ, 3 ≤ M →
    (∀ N : ℕ, (M : ℝ) > 2 * (Real.sqrt 2) ^ N →
      ∀ n : ℕ, n ≤ N →
        ∀ x : ℝ, 0 < x →
          0 < (-1 : ℝ) ^ n * iteratedDeriv n (kM M) x) ∧
    isSymmetricSelfDecomposable
      (fun t : ℝ => (yM M (t : ℂ))⁻¹) ∧
    retainsOffAxisQuartet (yM M)

/-- Each fixed member eventually fails complete monotonicity, and every
adverse derivative order has arbitrarily large points in the stated phase
class. -/
def claim15356 : Prop :=
  ∀ M : ℕ,
    (¬ completelyMonotoneOnPositive (kM M)) ∧
    ∀ n : ℕ, 2 * (Real.sqrt 2) ^ n > (M : ℝ) + 1 →
      ∀ R : ℝ, ∃ x : ℝ,
        R < x ∧ 0 < x ∧
          (∃ q : ℤ,
            x = Real.pi + (n : ℝ) * Real.pi / 4 +
              2 * Real.pi * (q : ℝ)) ∧
          (-1 : ℝ) ^ n * iteratedDeriv n (kM M) x < 0

end MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386
