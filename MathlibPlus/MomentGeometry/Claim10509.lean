import Mathlib

namespace MathlibPlus.MomentGeometry

/-- Claim 10509: the shape-one completed gamma Bezout matrix has the
 displayed positive rank-two determinant, while its rank-three determinant is
 negative. -/
theorem gammaLawRankTwoThreeCounterexample_claim10509 :
    let m : ℕ → ℚ := fun j ↦ j.factorial
    let h : ℕ → ℚ := fun j ↦ m j / (2 * j).factorial
    let completedBezout : (N : ℕ) → Matrix (Fin N) (Fin N) ℚ := fun _ i j ↦
      ∑ k ∈ Finset.range (min (i : ℕ) (j : ℕ) + 1),
        (i + j + 1 - 2 * k : ℕ) * h k * h (i + j + 1 - k)
    (completedBezout 2) 0 0 = 1 / 2 ∧
      (completedBezout 2) 0 1 = 1 / 6 ∧
      (completedBezout 2) 1 0 = 1 / 6 ∧
      (completedBezout 2) 1 1 = 1 / 15 ∧
      (completedBezout 2).det = 1 / 180 ∧
      (completedBezout 3).det = -1 / 23814000 := by
  native_decide

end MathlibPlus.MomentGeometry
