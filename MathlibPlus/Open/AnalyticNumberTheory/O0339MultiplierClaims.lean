import Mathlib
import MathlibPlus.Open.AnalyticNumberTheory.CompactDistributionMoments

open Set TopologicalSpace Filter
open scoped BigOperators Distributions
open MathlibPlus.Open.AnalyticNumberTheory.CompactDistributionMoments

namespace MathlibPlus.Open.AnalyticNumberTheory.O0339MultiplierClaims

noncomputable section

abbrev ComplexDistribution := Distribution (⊤ : Opens ℝ) ℂ ⊤
abbrev RealTestFunction := TestFunction (⊤ : Opens ℝ) ℝ ⊤

/-- The distributional carrier is compact and its support is contained in the
actual interval `[-A,A]`; the radius is not an unrelated free parameter. -/
def compactSupportIn (T : ComplexDistribution) (A : ℝ) : Prop :=
  0 ≤ A ∧ IsCompact (Distribution.dsupport T) ∧
    Distribution.dsupport T ⊆ Set.Icc (-A) A

/-- Reality of a complex-valued distribution on every real test function. -/
def isRealDistribution (T : ComplexDistribution) : Prop :=
  ∀ φ : RealTestFunction, (T φ).im = 0

/-- The polynomial-times-exponential bound of exponential type at most `A`. -/
def exponentialTypeBound (M : ℂ → ℂ) (A : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ z : ℂ,
    ‖M z‖ ≤ C * (1 + ‖z‖) ^ N * Real.exp (A * ‖z‖)

/-- Claim 15528: the canonical distributional exponential multiplier is entire
and of the stated type for every compactly supported distribution; only its
real-axis reality is conditional on the distribution being real. -/
def claim15528 : Prop :=
  ∀ (T : ComplexDistribution) (A : ℝ),
    compactSupportIn T A →
      ∃ M : ℂ → ℂ,
        Differentiable ℂ M ∧
          exponentialTypeBound M A ∧
          (∀ z : ℂ, M z ∈ compactDistributionMultiplierValues T z) ∧
          (isRealDistribution T → ∀ x : ℝ, (M (x : ℂ)).im = 0)

/-- A finite zero divisor in a disk, with the analytic order at each zero. -/
def hasLinearZeroDivisorBound (M : ℂ → ℂ) : Prop :=
  ∃ K R₀ : ℝ, 0 ≤ K ∧ 0 ≤ R₀ ∧
    ∀ R : ℝ, R₀ ≤ R →
      ∃ Z : Finset ℂ,
        (∀ z : ℂ,
          z ∈ Z ↔ z ≠ 0 ∧ ‖z‖ ≤ R ∧ M z = 0) ∧
        (∑ z ∈ Z, (analyticOrderNatAt M z : ℝ)) ≤ K * R

/-- The usual prime-counting function at a real cutoff. -/
def primeCountingAt (x : ℝ) : ℕ :=
  (Finset.filter (fun p : ℕ => Nat.Prime p ∧ (p : ℝ) ≤ x)
      (Finset.range (Nat.floor x + 1))).card

/-- Prime logarithms have the exponential density used in the Jensen
contradiction. -/
def primeLogExponentialDensity : Prop :=
  Asymptotics.IsEquivalent atTop
    (fun R : ℝ => (primeCountingAt (Real.exp R) : ℝ))
    (fun R : ℝ => Real.exp R / R)

/-- Claim 15533: Jensen's zero bound counts the zero divisor with
multiplicity, and the same compact-distribution multiplier cannot vanish on
all prime logarithms unless both the multiplier and the distribution vanish. -/
def claim15533 : Prop :=
  (∀ M : ℂ → ℂ,
    M ≠ 0 →
      Differentiable ℂ M →
        (∃ A : ℝ, exponentialTypeBound M A) →
          hasLinearZeroDivisorBound M) ∧
  primeLogExponentialDensity ∧
  (∀ (T : ComplexDistribution) (A : ℝ),
    compactSupportIn T A →
      ∃ M : ℂ → ℂ,
        Differentiable ℂ M ∧
          exponentialTypeBound M A ∧
          (∀ z : ℂ, M z ∈ compactDistributionMultiplierValues T z) ∧
          ((∀ p : ℕ, Nat.Prime p →
              M (Real.log (p : ℝ) : ℂ) = 0) →
            (∀ z : ℂ, M z = 0) ∧ T = 0))

end

end MathlibPlus.Open.AnalyticNumberTheory.O0339MultiplierClaims
