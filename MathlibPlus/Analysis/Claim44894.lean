import Mathlib

namespace MathlibPlus.Analysis.Claim44894

/-!
Formalization of the exact rational block-area formula and its first violation
at `n = 5` from admitted claim 44894.  The source-specific posterior-variance
carrier is not assigned a new meaning; the displayed formula is retained
literally.
-/

/-- The displayed block-area formula is at most one through `n = 4`, and its
first displayed violation is `B₅ = 813/800 > 1`. -/
theorem equalSharedSelectorAreaFirstViolation_44894 :
    let B : ℕ → ℚ := fun n =>
      ((n : ℚ) + 1) / (4 * n) +
        (1 / (2 * (n : ℚ) ^ 2)) *
          Finset.sum (Finset.range n)
            (fun r => ((n - r : ℕ) : ℚ) ^ 2 / (2 : ℚ) ^ r)
    B 1 ≤ 1 ∧ B 2 ≤ 1 ∧ B 3 ≤ 1 ∧ B 4 ≤ 1 ∧
      B 5 = (813 : ℚ) / 800 ∧ 1 < B 5 := by
  dsimp
  norm_num [Finset.sum_range_succ]

end MathlibPlus.Analysis.Claim44894
