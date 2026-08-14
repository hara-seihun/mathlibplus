import Mathlib

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace MathlibPlus.Open.Research.R2610

/-- Ordered positive factor pairs of a positive product shell. -/
def positiveFactorPairs (k : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 k).product (Finset.Icc 1 k)).filter
    (fun p => p.1 * p.2 = k)

/-- The shell coefficient written using the principal complex logarithm. -/
def tau (a : ℝ) (k : ℕ) : ℂ :=
  ∑ p ∈ positiveFactorPairs k,
    Complex.cpow ((p.2 : ℂ) / (p.1 : ℂ))
      (-Complex.I * (a : ℂ))

/-- The ordered-factor-pair count of a product shell. -/
def divisorCount (k : ℕ) : ℕ :=
  ∑ _p ∈ positiveFactorPairs k, (1 : ℕ)

/-- The sum of squared logarithmic ratios over ordered factor pairs. -/
def divisorLogSquare (k : ℕ) : ℝ :=
  ∑ p ∈ positiveFactorPairs k,
    (Real.log ((p.2 : ℝ) / (p.1 : ℝ))) ^ 2

/-- Claim 42791: the three product-shell arithmetic coefficients. -/
def claim42791 : Prop :=
  ∀ (a : ℝ) (k : ℕ), 0 < k →
    tau a k =
        ∑ p ∈ positiveFactorPairs k,
          Complex.cpow ((p.2 : ℂ) / (p.1 : ℂ))
            (-Complex.I * (a : ℂ)) ∧
    divisorCount k = ∑ _p ∈ positiveFactorPairs k, (1 : ℕ) ∧
    divisorLogSquare k =
      ∑ p ∈ positiveFactorPairs k,
        (Real.log ((p.2 : ℝ) / (p.1 : ℝ))) ^ 2

/-- The first-shell integrand appearing in the positive/negative bounds. -/
def firstShellIntegrand (u : ℝ) : ℝ :=
  u ^ 2 * (13 - 12 * Real.cosh u) * Real.exp (-2 * Real.cosh u)

/-- Claim 42798: support and integral bound for the positive part. -/
def claim42798 : Prop :=
  Real.cosh ((1 : ℝ) / 2) > (9 : ℝ) / 8 ∧
    (9 : ℝ) / 8 > (13 : ℝ) / 12 ∧
    (∀ u : ℝ, 0 ≤ u → (1 : ℝ) / 2 < u →
      max (firstShellIntegrand u) 0 = 0) ∧
    (∫ u in Set.Ici (0 : ℝ), max (firstShellIntegrand u) 0 ∂volume)
      ≤ Real.exp (-2) / 24

/-- Claim 42799: the negative-interval bounds for the first-shell integrand. -/
def claim42799 : Prop :=
  (∀ u ∈ Set.Icc (1 : ℝ) ((3 : ℝ) / 2),
      Real.cosh u > (37 : ℝ) / 24 ∧
      Real.cosh u < 3 ∧
      1 ≤ u ^ 2) ∧
    (∀ u ∈ Set.Icc (1 : ℝ) ((3 : ℝ) / 2),
      firstShellIntegrand u < -(11 : ℝ) / 2 * Real.exp (-6)) ∧
    (∫ u in Set.Icc (1 : ℝ) ((3 : ℝ) / 2), firstShellIntegrand u ∂volume)
      < -(11 : ℝ) / 4 * Real.exp (-6)

end MathlibPlus.Open.Research.R2610
