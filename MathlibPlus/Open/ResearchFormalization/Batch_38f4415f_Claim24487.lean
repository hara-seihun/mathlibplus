import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim24487

private def interiorGap (α : Fin 27 → ℝ) (i : Fin 27) : ℝ :=
  4 - α i

private def interiorGapMoment (α : Fin 27 → ℝ) (k : Fin 5) : ℝ :=
  ∑ i : Fin 27, (interiorGap α i) ^ k.1

private def interiorGapMoments (α : Fin 27 → ℝ) : Fin 5 → ℝ :=
  interiorGapMoment α

private def hankel3 (m : Fin 5 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => m ⟨i.1 + j.1, by omega⟩

/-- Strict positivity of the 3-by-3 Hankel matrix of the 27 positive
    interior gaps gives the exact Schur-complement lower bound for m₄. -/
def claim24487 : Prop :=
  ∀ (δ : ℝ) (α : Fin 27 → ℝ),
    0 < δ →
    (∀ i : Fin 27, 0 < α i ∧ α i < 4) →
    Matrix.PosDef (hankel3 (interiorGapMoments α)) →
      interiorGapMoments α 4 >
        (27 * (interiorGapMoments α 3) ^ 2 -
          2 * interiorGapMoments α 1 * interiorGapMoments α 2 *
            interiorGapMoments α 3 +
          (interiorGapMoments α 2) ^ 3) /
          (27 * interiorGapMoments α 2 -
            (interiorGapMoments α 1) ^ 2)

end MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim24487
