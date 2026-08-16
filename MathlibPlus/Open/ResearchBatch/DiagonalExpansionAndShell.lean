import Mathlib
import MathlibPlus.Open.ResearchBatch.Kernels

namespace MathlibPlus.Open.ResearchBatch

noncomputable section
open scoped BigOperators

/-- The coprime Dirichlet series used for the finite-modulus zeta factor. -/
def incompleteZeta (N m : ℕ) : ℝ :=
  ∑' n : {n : ℕ // 0 < n ∧ Nat.Coprime n N},
    1 / ((n.1 : ℝ) ^ m)

/-- The kth correction term in the diagonal expansion, for k ≥ 1. -/
def diagonalCorrectionTerm (N k : ℕ) : ℝ :=
  ((Nat.totient N : ℝ) / (N : ℝ)) *
    (((-1 : ℝ) ^ (k + 1)) /
      ((k : ℝ) * (N : ℝ) ^ k * incompleteZeta N (k + 1)))

def diagonalCorrectionSeries (N : ℕ) : ℝ :=
  ∑' k : {k : ℕ // 1 ≤ k}, diagonalCorrectionTerm N k.1

/-- Claim 13970: the convergent diagonal expansion at λ = N. -/
def diagonalScalingExpansion_claim13970 : Prop :=
  ∀ N : ℕ, Squarefree N → 2 ≤ N →
    Summable (fun k : {k : ℕ // 1 ≤ k} => diagonalCorrectionTerm N k.1) ∧
      MathlibPlus.Open.ResearchBatch.Kernels.boundaryScalingConstant N (N : ℝ) =
        1 - diagonalCorrectionSeries N

/-- Claim 13971: alternating decreasing corrections, bounds, and the diagonal asymptotic. -/
def diagonalAlternatingBounds_claim13971 : Prop :=
  ∀ N : ℕ, Squarefree N → 2 ≤ N →
    (∀ k : ℕ, 1 ≤ k →
      diagonalCorrectionTerm N (k + 1) * diagonalCorrectionTerm N k < 0 ∧
        |diagonalCorrectionTerm N (k + 1)| < |diagonalCorrectionTerm N k|) ∧
    1 - (Nat.totient N : ℝ) /
          ((N : ℝ) ^ 2 * incompleteZeta N 2) <
        MathlibPlus.Open.ResearchBatch.Kernels.boundaryScalingConstant N (N : ℝ) ∧
    MathlibPlus.Open.ResearchBatch.Kernels.boundaryScalingConstant N (N : ℝ) < 1 ∧
    (∃ B : ℝ, ∀ M : ℕ, Squarefree M → 2 ≤ M →
      |MathlibPlus.Open.ResearchBatch.Kernels.boundaryScalingConstant M (M : ℝ)| ≤ B) ∧
    Asymptotics.IsBigO
      (Filter.atTop ⊓ Filter.principal {M : ℕ | Squarefree M})
      (fun M : ℕ =>
        MathlibPlus.Open.ResearchBatch.Kernels.boundaryScalingConstant M (M : ℝ) - 1)
      (fun M : ℕ => 1 / (M : ℝ))

/-- The first-shell contribution on [1, 3/2], before its outer factor four. -/
def firstShellIntervalContribution : ℝ :=
  intervalIntegral
    (fun u : ℝ => u ^ 2 * (13 - 12 * Real.cosh u) *
      Real.exp (-2 * Real.cosh u))
    (1 : ℝ) (3 / 2 : ℝ) MeasureTheory.volume

/-- Claim 14052: the explicit negative contribution of the first shell interval. -/
def explicitNegativeIntervalBound_claim14052 : Prop :=
  (∀ u : ℝ, 1 ≤ u → u ≤ (3 / 2 : ℝ) →
    Real.cosh u ≥ Real.cosh 1) ∧
  Real.cosh 1 > (37 / 24 : ℝ) ∧
  (∀ u : ℝ, 1 ≤ u → u ≤ (3 / 2 : ℝ) →
    12 * Real.cosh u - 13 > (11 / 2 : ℝ)) ∧
  Real.cosh (3 / 2 : ℝ) < 3 ∧
  firstShellIntervalContribution < -11 * Real.exp (-6) / 4

end
end MathlibPlus.Open.ResearchBatch
