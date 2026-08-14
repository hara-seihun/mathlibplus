import Mathlib

noncomputable section

namespace MathlibPlus.Open.Research.AnalyticZerosBatch

/-- Claim 2546: a sign-changing analytic real zero has odd multiplicity. -/
def claim_2546 : Prop :=
  let hasZeroMultiplicity : (ℂ → ℂ) → ℂ → ℕ → Prop := fun F x m =>
    iteratedDeriv m F x ≠ 0 ∧
      ∀ k : ℕ, k < m → iteratedDeriv k F x = 0
  let changesSignAt : (ℝ → ℝ) → ℝ → Prop := fun g x =>
    ∃ ε : ℝ, 0 < ε ∧
      ((
          (∀ y : ℝ, x - ε < y → y < x → g y < 0) ∧
            (∀ y : ℝ, x < y → y < x + ε → 0 < g y)) ∨
        (
          (∀ y : ℝ, x - ε < y → y < x → 0 < g y) ∧
            (∀ y : ℝ, x < y → y < x + ε → g y < 0)))
  ∀ (F : ℂ → ℂ) (x : ℝ),
    AnalyticAt ℂ F (x : ℂ) →
    (∀ y : ℝ, (F (y : ℂ)).im = 0) →
    (¬ ∃ ε : ℝ, 0 < ε ∧
      ∀ z : ℂ, ‖z - (x : ℂ)‖ < ε → F z = 0) →
    F (x : ℂ) = 0 →
    changesSignAt (fun y : ℝ => (F (y : ℂ)).re) x →
    ∃ m : ℕ, 0 < m ∧ Odd m ∧ hasZeroMultiplicity F (x : ℂ) m

end MathlibPlus.Open.Research.AnalyticZerosBatch
