import Mathlib
import MathlibPlus.Open.Analysis.O0336.Claim15511
import MathlibPlus.Open.Analysis.O0336.Claim15513

open MeasureTheory Set
open scoped BigOperators MeasureTheory Topology

namespace MathlibPlus.Open.ResearchFormalization.O0336.ContinuousPositivePrimeBranch15516

noncomputable section

/-- The exact Lebesgue shift measure on the closed interval `[0,h]`. -/
noncomputable def shiftMeasure (h : ℝ) : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) h)

/-- The shifted logarithm on the right-half-plane germ, using the normalized
right-half-plane branch of `log ζ`. -/
noncomputable def continuousPositiveShiftLog (h : ℝ) (s : ℂ) : ℂ :=
  ∫ α : ℝ,
    MathlibPlus.Open.Analysis.O0336.Claim15511.zetaLog
      (s + (α : ℂ)) ∂shiftMeasure h

/-- The actual shifted-zeta exponential attached to Lebesgue measure on
`[0,h]`. -/
noncomputable def continuousPositiveShift (h : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (continuousPositiveShiftLog h s)

/-- The Laplace-transform value of the exact shift measure at a prime. -/
noncomputable def primeCoefficient (h : ℝ) (p : ℕ) : ℝ :=
  ∫ α : ℝ, Real.rpow (p : ℝ) (-α) ∂shiftMeasure h

/-- The slit neighborhood of the origin on which the two displayed
logarithms are taken as the principal logarithms. -/
def slitDisk (h r : ℝ) : Set ℂ :=
  {z : ℂ |
    z ∈ Metric.ball (0 : ℂ) r ∧
      ¬ (z.im = 0 ∧ z.re ≤ 0) ∧
        ¬ ((z + (h : ℂ)).im = 0 ∧ (z + (h : ℂ)).re ≤ 0)}

/-- The ordinary Dirichlet-series carrier and its prime coefficients for the
same shifted exponential. -/
def HasOrdinaryPrimeCoefficients (h : ℝ) : Prop :=
  ∃ (σ₀ : ℝ) (b : ℕ+ → ℂ),
    1 < σ₀ ∧
      MathlibPlus.Open.Analysis.O0336.Claim15513.HasOrdinaryDirichletExpansion
        (continuousPositiveShift h) b σ₀ ∧
        ∀ (p : ℕ) (hp : Nat.Prime p),
          b ⟨p, Nat.Prime.pos hp⟩ = (primeCoefficient h p : ℂ)

/-- Claim 15516: Lebesgue measure on `[0,h]` gives the exact positive prime
coefficient, while the right-half-plane germ of its shifted-zeta product has
the displayed logarithmic branch expansion and no nonzero meromorphic
continuation through `s=1`. -/
def claim15516_explicitContinuousPositivePrimeBranchPoint : Prop :=
  ∀ h : ℝ,
    0 < h →
      (∃ (σ₀ : ℝ) (b : ℕ+ → ℂ),
        1 < σ₀ ∧
          MathlibPlus.Open.Analysis.O0336.Claim15513.HasOrdinaryDirichletExpansion
            (continuousPositiveShift h) b σ₀ ∧
          ∀ (p : ℕ) (hp : Nat.Prime p),
            b ⟨p, Nat.Prime.pos hp⟩ =
                (primeCoefficient h p : ℂ) ∧
              primeCoefficient h p =
                (1 - Real.rpow (p : ℝ) (-h)) / Real.log (p : ℝ) ∧
              0 < primeCoefficient h p) ∧
      ∃ r : ℝ,
        0 < r ∧
          r < h ∧
          ∃ L A B : ℂ → ℂ,
            AnalyticOnNhd ℂ L (slitDisk h r) ∧
              AnalyticOnNhd ℂ A (slitDisk h r) ∧
                AnalyticOnNhd ℂ B (slitDisk h r) ∧
                  (∀ z : ℂ, z ∈ slitDisk h r →
                    0 < z.re →
                      L z =
                        continuousPositiveShiftLog h ((1 : ℂ) + z)) ∧
                    (∀ z : ℂ, z ∈ slitDisk h r →
                      L z =
                        z * Complex.log z -
                          (z + (h : ℂ)) * Complex.log (z + (h : ℂ)) +
                            (h : ℂ) + A z) ∧
                    (∀ z : ℂ, z ∈ slitDisk h r →
                      B z = -deriv A z) ∧
                    (∀ z : ℂ, z ∈ slitDisk h r →
                      -deriv (fun w : ℂ => Complex.exp (L w)) z /
                          Complex.exp (L z) =
                        Complex.log (z + (h : ℂ)) -
                          Complex.log z + B z) ∧
                    (¬ ∃ M : ℂ → ℂ,
                      MeromorphicOn M (Metric.ball (1 : ℂ) r) ∧
                        (∃ w : ℂ,
                          w ∈ Metric.ball (1 : ℂ) r ∧ M w ≠ 0) ∧
                        (∀ s : ℂ,
                          s ∈ Metric.ball (1 : ℂ) r →
                            1 < s.re →
                              M s = continuousPositiveShift h s))

end

end MathlibPlus.Open.ResearchFormalization.O0336.ContinuousPositivePrimeBranch15516
