import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim17817

/-- Claim 17817: every interval-reflection entry is zero or the positive
weight `b-a`. -/
theorem intervalReflectionEntries_claim17817 {N a b : ℕ} (hab : a < b)
    (_hbN : b ≤ N) :
    let R : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := fun i j =>
      if (i.val + j.val = a + b - 1 ∧
          a ≤ i.val ∧ i.val < b ∧ a ≤ j.val ∧ j.val < b) then
        (b - a : ℝ)
      else 0
    ∀ i j, R i j = 0 ∨
      (0 < R i j ∧ R i j = (b - a : ℝ)) := by
  dsimp
  intro i j
  by_cases h : (i.val + j.val = a + b - 1 ∧
      a ≤ i.val ∧ i.val < b ∧ a ≤ j.val ∧ j.val < b)
  · right
    simp [h]
    exact_mod_cast hab
  · left
    simp [h]

end MathlibPlus.LinearAlgebra.Claim17817
