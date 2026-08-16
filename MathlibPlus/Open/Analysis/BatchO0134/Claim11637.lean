import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.BatchO0134.Claim11637

private def falling (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => falling a n * (a - n)

private def generalizedBinomial (a : ℝ) (n : ℕ) : ℝ :=
  falling a n / (Nat.factorial n : ℝ)

private def generalizedLaguerre (α : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    (-1 : ℝ) ^ k * generalizedBinomial (m + α) (m - k) * x ^ k /
      (Nat.factorial k : ℝ)

private def heatKernel (m : ℕ) (t u : ℝ) : ℝ :=
  (Nat.factorial m : ℝ) / (2 * Real.sqrt Real.pi) *
      Real.rpow t (-(m : ℝ) - (1 : ℝ) / 2) *
      Real.exp (-(u ^ 2) / (4 * t)) *
      generalizedLaguerre (-(1 : ℝ) / 2) m (u ^ 2 / (4 * t))

private def iteratedDerivative (m : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  Nat.rec f (fun _ g => deriv g) m

private def heatGaussian (u t : ℝ) : ℝ :=
  Real.exp (-(u ^ 2) / (4 * t)) / (2 * Real.sqrt (Real.pi * t))

def gammaWindowedHeatDerivativeKernel : Prop :=
  ∀ (m : ℕ) (t u : ℝ),
    0 < t →
      heatKernel m t u =
        (-1 : ℝ) ^ m * iteratedDerivative m (fun s : ℝ => heatGaussian u s) t

end MathlibPlus.Open.Analysis.BatchO0134.Claim11637
