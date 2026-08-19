import MathlibPlus.Open.Analysis.BatchO0134.Claim11637
import MathlibPlus.Open.Analysis.BatchO0134.Claim11640
import MathlibPlus.Open.Analysis.BatchO0134.Claim11648

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis.BatchO0134.Claim11646

private def falling (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => falling a n * (a - n)

private def generalizedBinomial (a : ℝ) (n : ℕ) : ℝ :=
  falling a n / (Nat.factorial n : ℝ)

private def generalizedLaguerre (α : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    (-1 : ℝ) ^ k * generalizedBinomial (m + α) (m - k) * x ^ k /
      (Nat.factorial k : ℝ)

private def profile (m : ℕ) (σ r : ℝ) : ℝ :=
  Real.rpow r (3 - 2 * σ) * Real.exp (-(r ^ 2)) *
    generalizedLaguerre ((1 : ℝ) / 2) m (r ^ 2)

private def autocorrelation (m : ℕ) (σ d : ℝ) : ℝ :=
  2 * ∫ s : ℝ, profile m σ (Real.exp (s + d)) * profile m σ (Real.exp s)

private def fourierMultiplier (m : ℕ) (σ τ : ℝ) : ℂ :=
  ∫ d : ℝ,
    Complex.ofReal (autocorrelation m σ d) *
      Complex.exp (-Complex.I * Complex.ofReal (τ * d))

private def risingFactor (z : ℂ) (m : ℕ) : ℂ :=
  ∏ j ∈ Finset.range m, (z + (j : ℂ))

private def profileCoefficient (m : ℕ) (σ τ : ℝ) : ℂ :=
  Complex.Gamma
      (Complex.ofReal ((3 : ℝ) / 2 - σ) -
        Complex.I * Complex.ofReal (τ / 2)) *
    risingFactor
      (Complex.ofReal σ + Complex.I * Complex.ofReal (τ / 2)) m /
      (2 * (Nat.factorial m : ℂ))

def exactFourierMultiplier : Prop :=
  ∀ (m : ℕ) (σ τ : ℝ),
    (1 : ℝ) / 2 < σ →
    σ < (3 : ℝ) / 2 →
      fourierMultiplier m σ τ =
          Complex.ofReal
            ((Complex.normSq
                (Complex.Gamma
                  (Complex.ofReal ((3 : ℝ) / 2 - σ) +
                    Complex.I * Complex.ofReal (τ / 2))) *
              Complex.normSq
                (risingFactor
                  (Complex.ofReal σ + Complex.I * Complex.ofReal (τ / 2)) m)) /
              (2 * (Nat.factorial m : ℝ) ^ 2)) ∧
        fourierMultiplier m σ τ =
          Complex.ofReal (2 * Complex.normSq (profileCoefficient m σ τ)) ∧
        0 ≤
          (Complex.normSq
              (Complex.Gamma
                (Complex.ofReal ((3 : ℝ) / 2 - σ) +
                  Complex.I * Complex.ofReal (τ / 2))) *
            Complex.normSq
              (risingFactor
                (Complex.ofReal σ + Complex.I * Complex.ofReal (τ / 2)) m)) /
            (2 * (Nat.factorial m : ℝ) ^ 2)

end MathlibPlus.Open.Analysis.BatchO0134.Claim11646
