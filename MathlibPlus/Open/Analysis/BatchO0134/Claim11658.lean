import MathlibPlus.Open.Analysis.BatchO0134.Claim11648

open MeasureTheory
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.BatchO0134.Claim11658

noncomputable section

private def falling (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => falling a n * (a - n)

private def generalizedBinomial (a : ℝ) (n : ℕ) : ℝ :=
  falling a n / (Nat.factorial n : ℝ)

private def generalizedLaguerre (α : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    (-1 : ℝ) ^ k * generalizedBinomial ((m : ℝ) + α) (m - k) * x ^ k /
      (Nat.factorial k : ℝ)

private def profile (m : ℕ) (σ r : ℝ) : ℝ :=
  Real.rpow r (3 - 2 * σ) * Real.exp (-(r ^ 2)) *
    generalizedLaguerre ((1 : ℝ) / 2) m (r ^ 2)

private def autocorrelation (m : ℕ) (σ d : ℝ) : ℝ :=
  2 * ∫ s : ℝ,
    profile m σ (Real.exp (s + d)) * profile m σ (Real.exp s)

private def fourierMultiplier (m : ℕ) (σ τ : ℝ) : ℝ :=
  ∫ d : ℝ, autocorrelation m σ d * Real.cos (τ * d)

private def normalizedMultiplier (m : ℕ) (τ : ℝ) : ℝ :=
  Real.exp (2 * (m : ℝ)) * (Nat.factorial m : ℝ) ^ 2 /
      (4 * Real.pi * (m : ℝ) ^ (2 * m + 2)) *
    fourierMultiplier m 1 τ

/-- The sigma-one homogeneous coefficient times the autocorrelation Fourier
multiplier is the displayed normalized all-order product. -/
def claim11658 : Prop :=
  ∀ (m : ℕ) (τ : ℝ), 1 ≤ m →
    normalizedMultiplier m τ =
      Real.exp (2 * (m : ℝ)) /
        (8 * (m : ℝ) ^ (2 * m + 2) * Real.cosh (Real.pi * τ / 2)) *
        Finset.prod (Finset.Icc (1 : ℕ) m) (fun j =>
          (j : ℝ) ^ 2 + τ ^ 2 / 4)

end

end MathlibPlus.Open.Analysis.BatchO0134.Claim11658
