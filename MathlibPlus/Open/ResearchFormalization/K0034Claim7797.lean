import MathlibPlus.Open.Analysis.RankinRadialBatch

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.K0034Claim7797

noncomputable section

/-- The Schur pivots and inertia of the one-sided Gamma--Rankin Hankel matrix. -/
def claim7797 : Prop :=
  ∀ (α : ℝ), 0 < α →
    let H : ∀ m : ℕ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
      fun m => MathlibPlus.Open.Analysis.radialHankel α m
        (MathlibPlus.Open.Analysis.radialJet α)
    let leadingSchurPivot : ℕ → ℝ := fun j =>
      if j = 0 then Matrix.det (H 0)
      else Matrix.det (H j) / Matrix.det (H (j - 1))
    let delta : ℕ → ℝ := fun j =>
      (-1 : ℝ) ^ j * ((4 : ℝ)⁻¹) ^ j * (j.factorial : ℝ) *
        MathlibPlus.Open.Analysis.risingFactorial α j
    let hasInertia : ∀ (m p q : ℕ), Prop := fun m p q =>
      p + q = m + 1 ∧
        ∃ P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ,
          Matrix.det P ≠ 0 ∧
            Matrix.transpose P * H m * P =
              Matrix.diagonal (fun i =>
                if i.val < p then (1 : ℝ) else -1)
    (∀ j : ℕ, leadingSchurPivot j = delta j) ∧
      (∀ m : ℕ, hasInertia m (m / 2 + 1) ((m + 1) / 2)) ∧
        hasInertia 3 2 2 ∧ ¬ hasInertia 3 3 1

end

end MathlibPlus.Open.ResearchFormalization.K0034Claim7797
