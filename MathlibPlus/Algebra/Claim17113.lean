import Mathlib

namespace MathlibPlus.Algebra.Claim17113

/-- The sum of the cell widths `2 n + 1` on an inclusive interval. -/
theorem widthSum_identity (N₀ M : ℕ) (hN : N₀ ≤ M) :
    ∑ n ∈ Finset.Icc N₀ M, (2 * (n : ℝ) + 1) =
      (M + 1 : ℝ)^2 - (N₀ : ℝ)^2 := by
  have hsum (n : ℕ) :
      ∑ k ∈ Finset.range n, (2 * (k : ℝ) + 1) = (n : ℝ)^2 := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
  rw [← Finset.Ico_succ_right_eq_Icc N₀ M]
  have hI := Finset.sum_Ico_eq_sub
      (f := fun n : ℕ => 2 * (n : ℝ) + 1)
      (m := N₀) (n := M + 1) (by omega)
  change (∑ n ∈ Finset.Ico N₀ (M + 1), (2 * (n : ℝ) + 1)) = _
  rw [hI]
  rw [hsum (M + 1), hsum N₀]
  push_cast
  ring

/-- Scaling every width by the same base-cell factor scales the total by the
same factor; choosing the denominator gives the endpoint convention in the
source cost formula. -/
theorem scaledWidthCost_identity (C b : ℝ) (N₀ M : ℕ) (hN : N₀ ≤ M)
    (hb : b ≠ 0) :
    C / b * (∑ n ∈ Finset.Icc N₀ M, (2 * (n : ℝ) + 1)) =
      C * (((M + 1 : ℝ)^2 - (N₀ : ℝ)^2) / b) := by
  rw [widthSum_identity N₀ M hN]
  field_simp [hb]

end MathlibPlus.Algebra.Claim17113
