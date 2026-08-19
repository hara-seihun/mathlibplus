import MathlibPlus.Open.Analysis.BatchO0134.Claim11637
import MathlibPlus.Open.Analysis.BatchO0134.Claim11640
import MathlibPlus.Open.Analysis.BatchO0134.Claim11648

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis.BatchO0134.Claim11642

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

private def energy (m : ℕ) (σ : ℝ) (C : ℝ → ℝ) : ℝ :=
  (Real.exp (2 * (m : ℝ)) /
      Real.rpow (m : ℝ) (2 * (m : ℝ) + 2 * σ)) *
    ∫ t in Set.Ioi (0 : ℝ),
      Real.rpow t (2 * (m : ℝ) + 2 * σ - 1) *
        (abs (∫ u in Set.Ioi (0 : ℝ),
          C u * deriv (fun v : ℝ => heatKernel m t v) u)) ^ 2

private def energyConstant (m : ℕ) (σ : ℝ) : ℝ :=
  Real.exp (2 * (m : ℝ)) * (Nat.factorial m : ℝ) ^ 2 *
      Real.rpow 4 (1 - 2 * σ) /
    (Real.pi * Real.rpow (m : ℝ) (2 * (m : ℝ) + 2 * σ))

private def bilinearKernel (m : ℕ) (σ u v : ℝ) : ℝ :=
  u * v * ∫ z in Set.Ioi (0 : ℝ),
    Real.rpow z (2 - 2 * σ) * Real.exp (-(u ^ 2 + v ^ 2) * z) *
      generalizedLaguerre ((1 : ℝ) / 2) m (u ^ 2 * z) *
      generalizedLaguerre ((1 : ℝ) / 2) m (v ^ 2 * z)

def homogeneousBilinearKernelFormula : Prop :=
  ∀ (m : ℕ) (σ : ℝ) (C : ℝ → ℝ),
    Bornology.IsBounded (Set.range C) →
    HasCompactSupport C →
    (1 : ℝ) / 2 < σ →
    σ < (3 : ℝ) / 2 →
      energy m σ C =
        energyConstant m σ *
          ∫ u in Set.Ioi (0 : ℝ),
            ∫ v in Set.Ioi (0 : ℝ),
              C u * C v * bilinearKernel m σ u v

end MathlibPlus.Open.Analysis.BatchO0134.Claim11642
