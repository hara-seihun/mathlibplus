import Mathlib

namespace MathlibPlus.Algebra.Claim48839

/-- The exact rational data retained from the closest-nonclone audit witness.
The source-specific meanings of `closest`, `nonclone`, `R₀`, and the two defect
quantities are not supplied by the claim packet; this theorem records the
literal finite numerical certificate without inventing those carriers. -/
theorem exactNumericalCore_claim48839 :
    ∃ (w₀ w₁ w₂ w₃ : ℚ) (inserted o₀ o₁ o₂ : ℕ)
      (R₀ lhs rhs delta derivativeDefect : ℚ),
      w₀ = 1 / 8 ∧
      w₁ = 5 / 8 ∧
      w₂ = 1 / 8 ∧
      w₃ = 1 / 8 ∧
      inserted = 1 ∧
      o₀ = 3 ∧ o₁ = 2 ∧ o₂ = 4 ∧
      R₀ = 39 / 16 ∧
      lhs = 1771 / 4096 ∧
      rhs = 9 / 16 ∧
      delta = -533 / 4096 ∧
      derivativeDefect = -533 / 2048 ∧
      lhs < rhs := by
  refine ⟨1 / 8, 5 / 8, 1 / 8, 1 / 8, 1, 3, 2, 4,
    39 / 16, 1771 / 4096, 9 / 16, -533 / 4096, -533 / 2048, ?_⟩
  norm_num

end MathlibPlus.Algebra.Claim48839
