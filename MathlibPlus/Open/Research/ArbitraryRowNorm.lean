import Mathlib

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.Research

noncomputable def scaledLambertW (j : ℕ) : ℝ :=
  sInf {w : ℝ | 0 ≤ w ∧ w * Real.exp w = (j : ℝ) / (2 * Real.pi)}

def compactLambertCoefficient (j : ℕ) : ℝ :=
  scaledLambertW j / ((4 : ℝ) * (j : ℝ))

def relativeGauge (a : ℕ → ℝ) (j : ℕ) : ℝ :=
  Real.log (a j / compactLambertCoefficient j)

def adjacentGaugeDefect (a : ℕ → ℝ) (j : ℕ) : ℝ :=
  relativeGauge a j - relativeGauge a (j + 1)

def trailingLambertSum (m N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc (m + 1) N, (scaledLambertW N - scaledLambertW j)

def terminalGaugeCocycle (a : ℕ → ℝ) (m N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc (m + 1) N,
    (relativeGauge a j - relativeGauge a N)

def monicNormProduct (μ₀ : ℝ) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  μ₀ * ∏ j ∈ Finset.Icc 1 (2 * k), (a j) ^ 2

/-- Exact arbitrary-row norm identities from admitted Claim 8898. -/
noncomputable def exactArbitraryRowNormIdentities : Prop :=
  ∀ (N n m : ℕ) (a : ℕ → ℝ) (μ₀ : ℝ) (h : ℕ → ℝ),
    N = 2 * n →
    0 < n →
    m < N →
    Even m →
    0 < μ₀ →
    (∀ j, 1 ≤ j → j ≤ N → 0 < a j) →
    (∀ k, k ≤ n → h k = monicNormProduct μ₀ a k) →
    let cN : ℝ := a N
    Real.log (cN ^ (2 * (N - m)) * h (m / 2) / h (N / 2)) =
        -2 * (trailingLambertSum m N + terminalGaugeCocycle a m N) ∧
      Real.log (h n / (μ₀ * cN ^ (4 * n))) =
        2 * (trailingLambertSum 0 N + terminalGaugeCocycle a 0 N) ∧
      Real.log ((h n * h (n - 1)) /
          (μ₀ ^ 2 * cN ^ (8 * n - 4))) =
        4 * (trailingLambertSum 0 N + terminalGaugeCocycle a 0 N) -
          2 * (scaledLambertW N - scaledLambertW (N - 1) +
            adjacentGaugeDefect a (N - 1))

end MathlibPlus.Open.Research
