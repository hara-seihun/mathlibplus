import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.R0076

noncomputable section

/-- Claim 17720: the Volterra second-derivative chain. -/
def claim17720_volterraDerivativeChain
    (e : ℕ → ℝ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ y : ℝ,
    iteratedDeriv 2 (e (n + 1)) y = e n y

/-- Claim 17722: every level is positive on the common chamber. -/
def claim17722_commonPositivityChamber
    (e : ℕ → ℝ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ y : ℝ,
    0 < y → y < 2 * Real.sqrt 2 → 0 < e n y

/-- Claim 17723: all consecutive-level evaluation minors have the fixed
positive Vandermonde orientation in the common chamber. -/
def claim17723_allConsecutiveEvaluationMinorsPositive
    (e : ℕ → ℝ → ℝ) : Prop :=
  ∀ r h : ℕ, 1 ≤ r → 1 ≤ h →
    ∀ y : Fin h → ℝ,
      (∀ j : Fin h, 0 < y j ∧ y j < 2 * Real.sqrt 2) →
      (∀ i j : Fin h, i.1 < j.1 → y i < y j) →
      0 < Matrix.det
        (fun i j : Fin h ↦ e (r + i.1) (y j))

end

end MathlibPlus.Open.NewResearch2.R0076
