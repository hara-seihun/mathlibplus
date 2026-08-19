import MathlibPlus.Open.Analysis.BatchO0134.Claim11637
import MathlibPlus.Open.Analysis.BatchO0134.Claim11640
import MathlibPlus.Open.Analysis.BatchO0134.Claim11648

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.BatchO0134.Claim11639

private def falling (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => falling a n * (a - n)

private def generalizedBinomial (a : ℝ) (n : ℕ) : ℝ :=
  falling a n / (Nat.factorial n : ℝ)

private def generalizedLaguerre (α : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    (-1 : ℝ) ^ k * generalizedBinomial (m + α) (m - k) * x ^ k /
      (Nat.factorial k : ℝ)

private def heatGaussian (u t : ℝ) : ℝ :=
  Real.exp (-(u ^ 2) / (4 * t)) / (2 * Real.sqrt (Real.pi * t))

private def heatKernel (m : ℕ) (t u : ℝ) : ℝ :=
  (-1 : ℝ) ^ m *
    iteratedDeriv m (fun s : ℝ => heatGaussian u s) t

def spatialDerivativeFormula : Prop :=
  ∀ (m : ℕ) (t u : ℝ),
    0 < t →
      deriv (fun v : ℝ => heatKernel m t v) u =
        -((Nat.factorial m : ℝ) * u) / (4 * Real.sqrt Real.pi) *
          Real.rpow t (-(m : ℝ) - (3 : ℝ) / 2) *
          Real.exp (-(u ^ 2) / (4 * t)) *
          generalizedLaguerre ((1 : ℝ) / 2) m (u ^ 2 / (4 * t))

end MathlibPlus.Open.Analysis.BatchO0134.Claim11639
