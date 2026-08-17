import MathlibPlus.Open.Analysis.BatchO0134.Claim11648

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis.BatchO0134.Claim11644

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

private def homogeneousKernel (m : ℕ) (σ u v : ℝ) : ℝ :=
  u * v * ∫ z in Set.Ioi (0 : ℝ),
    Real.rpow z (2 - 2 * σ) * Real.exp (-(u ^ 2 + v ^ 2) * z) *
      generalizedLaguerre ((1 : ℝ) / 2) m (u ^ 2 * z) *
      generalizedLaguerre ((1 : ℝ) / 2) m (v ^ 2 * z)

private def profile (m : ℕ) (σ r : ℝ) : ℝ :=
  Real.rpow r (3 - 2 * σ) * Real.exp (-(r ^ 2)) *
    generalizedLaguerre ((1 : ℝ) / 2) m (r ^ 2)

private def autocorrelation (m : ℕ) (σ d : ℝ) : ℝ :=
  2 * ∫ s : ℝ,
    profile m σ (Real.exp (s + d)) * profile m σ (Real.exp s)

/-- In the Fubini strip, exponential coordinates turn the homogeneous
Laguerre kernel into the stated logarithmic autocorrelation. -/
def claim11644 : Prop :=
  ∀ (m : ℕ) (σ x y : ℝ),
    (1 : ℝ) / 2 < σ → σ < (3 : ℝ) / 2 →
      homogeneousKernel m σ (Real.exp x) (Real.exp y) =
        Real.rpow (Real.exp x * Real.exp y) (2 * σ - 2) *
          autocorrelation m σ (x - y)

end

end MathlibPlus.Open.Analysis.BatchO0134.Claim11644
