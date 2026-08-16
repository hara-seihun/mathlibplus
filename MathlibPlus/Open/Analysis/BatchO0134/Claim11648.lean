import Mathlib

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis.BatchO0134.Claim11648

private def falling (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => falling a n * (a - n)

private def generalizedBinomial (a : ℝ) (n : ℕ) : ℝ :=
  falling a n / (Nat.factorial n : ℝ)

private def generalizedLaguerre (α : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    (-1 : ℝ) ^ k * generalizedBinomial (m + α) (m - k) * x ^ k /
      (Nat.factorial k : ℝ)

private def phi (m : ℕ) (σ r : ℝ) : ℝ :=
  Real.rpow r (3 - 2 * σ) * Real.exp (-(r ^ 2)) *
    generalizedLaguerre ((1 : ℝ) / 2) m (r ^ 2)

private def autocorrelation (m : ℕ) (σ d : ℝ) : ℝ :=
  2 * ∫ s : ℝ, phi m σ (Real.exp (s + d)) * phi m σ (Real.exp s)

private def fourierMultiplier (m : ℕ) (σ τ : ℝ) : ℂ :=
  ∫ d : ℝ,
    Complex.ofReal (autocorrelation m σ d) *
      Complex.exp (-Complex.I * Complex.ofReal (τ * d))

private def productFactors (m : ℕ) (τ : ℝ) : ℝ :=
  ∏ j ∈ Finset.Icc (1 : ℕ) m, (j : ℝ) ^ 2 + τ ^ 2 / 4

def specializedMultiplierAtOne : Prop :=
  ∀ (m : ℕ) (τ : ℝ),
    fourierMultiplier m 1 τ =
      Complex.ofReal
        (Real.pi / (2 * (Nat.factorial m : ℝ) ^ 2 * Real.cosh (Real.pi * τ / 2)) *
          productFactors m τ)

end MathlibPlus.Open.Analysis.BatchO0134.Claim11648
