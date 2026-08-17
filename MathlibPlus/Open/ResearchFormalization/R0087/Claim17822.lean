import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0087.Claim17822

/-- Claim 17822: the exact two-cell interval-reflection block on `[0,2)` is
entrywise nonnegative but has determinant `-4`. -/
def claim17822 : Prop :=
  let R : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
    if (i.val + j.val = 0 + 2 - 1 ∧
        0 ≤ i.val ∧ i.val < 2 ∧
        0 ≤ j.val ∧ j.val < 2) then
      ((2 - 0 : ℕ) : ℝ)
    else 0
  (∀ i j, 0 ≤ R i j) ∧
    Matrix.det R = (-4 : ℝ)

end MathlibPlus.Open.ResearchFormalization.R0087.Claim17822
