import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatchR0253

open MeasureTheory

/-- The divided even moments of a (positive) measure on the real line. -/
noncomputable def dividedEvenMoment (μ : Measure ℝ) (j : ℕ) : ℝ :=
  ∫ x : ℝ, x ^ (2 * j) / (Nat.factorial (2 * j) : ℝ) ∂μ

/-- The shifted rank-`N` Hankel matrix of divided even moments. -/
noncomputable def shiftedRankNHankel (μ : Measure ℝ) (N s : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => dividedEvenMoment μ ((i : ℕ) + (j : ℕ) + s)

/-- The exact moment and shifted-Hankel specification. -/
def dividedEvenMomentsClaim : Prop :=
  ∀ (μ : Measure ℝ),
    ∃ h : ℕ → ℝ,
      (∀ j : ℕ,
        h j = ∫ x : ℝ, x ^ (2 * j) / (Nat.factorial (2 * j) : ℝ) ∂μ) ∧
      ∀ (N s : ℕ) (i j : Fin N),
        shiftedRankNHankel μ N s i j = h ((i : ℕ) + (j : ℕ) + s)

end MathlibPlus.Open.Research.FormalizationBatchR0253
