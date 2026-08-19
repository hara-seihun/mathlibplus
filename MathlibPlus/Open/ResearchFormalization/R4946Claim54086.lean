import Mathlib
import MathlibPlus.Open.Analysis.FiniteTraceIndistinguishability54091

open MathlibPlus.Open.Analysis.FiniteTraceIndistinguishability54091

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R4946

private noncomputable def originRow
    (τ : ℝ) (k : ℕ) (n : ℤ) : ℝ :=
  2 * (n : ℝ) ^ (2 * k) * Real.exp (τ * (n : ℝ) ^ 2)

private noncomputable def targetRow (n : ℤ) : ℝ :=
  -2 * Real.exp (targetTime * (n : ℝ) ^ 2) *
    Real.cosh ((n : ℝ) * targetHeight)

/-- R-4946 claim 54086: the target row is outside every finite complex span
of origin-time jet rows on the odd integer tail beginning at five. -/
def claim54086_targetRowOutsideFiniteSpan : Prop :=
  ∀ (m : ℕ) (τ : Fin m → ℝ) (k : Fin m → ℕ) (c : Fin m → ℂ),
    ∃ n : ℤ, Odd n ∧ 5 ≤ n ∧
      (targetRow n : ℂ) ≠
        ∑ j : Fin m, c j * (originRow (τ j) (k j) n : ℂ)

end MathlibPlus.Open.ResearchFormalization.R4946
