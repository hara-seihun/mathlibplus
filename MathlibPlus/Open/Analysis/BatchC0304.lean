import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.Analysis

private def associatedLaguerreTwo (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (-1 : ℝ) ^ k * (Nat.choose (n + 2) (n - k) : ℝ) * t ^ k /
      (Nat.factorial k : ℝ)

private def firstShiftLaguerreVector (n : ℕ) (t : ℝ) : ℝ :=
  if 2 ≤ n then associatedLaguerreTwo (n - 2) t else 0

private def poissonWeight (x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-x) * x ^ n / (Nat.factorial n : ℝ)

private def firstShiftGraphKernel (x t s : ℝ) : ℝ :=
  ∑' n : ℕ, poissonWeight x n *
    (firstShiftLaguerreVector n t * firstShiftLaguerreVector n s +
      firstShiftLaguerreVector (n + 1) t * firstShiftLaguerreVector (n + 1) s)

private def positiveCoefficientBivariate (P : MvPolynomial (Fin 2) ℝ) : Prop :=
  ∀ m ∈ P.support, 0 < P.coeff m

private def evaluateBivariate (P : MvPolynomial (Fin 2) ℝ) (t s : ℝ) : ℝ :=
  MvPolynomial.eval₂ (RingHom.id ℝ) (fun i => Fin.cases t (fun _ => s) i) P

/-- The effective-time graph-kernel bound. -/
def effectiveTimeGraphKernelBound4257 : Prop :=
  ∀ x : ℝ, 0 < x →
    ∃ P : MvPolynomial (Fin 2) ℝ,
      positiveCoefficientBivariate P ∧
        ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
          |firstShiftGraphKernel x t s| ≤
            evaluateBivariate P t s *
              Real.exp
                (3 * Real.rpow x (1 / 3) *
                    Real.rpow ((Real.sqrt t + Real.sqrt s) / 2) (4 / 3) -
                  2 * Real.rpow x (2 / 3) *
                    Real.rpow ((Real.sqrt t + Real.sqrt s) / 2) (2 / 3))

/-- The dyadic lower bound for the Jensen gap
`D(t,s) = (t^(2/3) + s^(2/3))/2 - ((sqrt t + sqrt s)/2)^(4/3)`.
-/
def dyadicJensenGapTransfer4261 : Prop :=
  ∀ (T t s : ℝ),
    0 < T →
    T ≤ t → t ≤ 2 * T →
    T ≤ s → s ≤ 2 * T →
    (Real.rpow t (2 / 3) + Real.rpow s (2 / 3)) / 2 -
          Real.rpow ((Real.sqrt t + Real.sqrt s) / 2) (4 / 3) ≥
      (t - s) ^ 2 /
        (144 * Real.rpow 2 (1 / 3) * Real.rpow T (4 / 3))

end MathlibPlus.Open.Analysis

end
