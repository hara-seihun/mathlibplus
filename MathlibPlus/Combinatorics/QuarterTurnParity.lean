import Mathlib

namespace MathlibPlus.Combinatorics.QuarterTurnParity

/-- Claim 21167: the necessary mod-four channel equation has no solution for
three signs. -/
theorem no_global_channel_orientation :
    ¬ ∃ ε₁₂ ε₂₃ ε₁₃ : ℤ,
      (ε₁₂ = -1 ∨ ε₁₂ = 1) ∧
        (ε₂₃ = -1 ∨ ε₂₃ = 1) ∧
          (ε₁₃ = -1 ∨ ε₁₃ = 1) ∧
            Int.ModEq 4 ε₁₃ (ε₁₂ + ε₂₃) := by
  rintro ⟨ε₁₂, ε₂₃, ε₁₃, h₁₂, h₂₃, h₁₃, hmod⟩
  rcases h₁₂ with rfl | rfl <;>
    rcases h₂₃ with rfl | rfl <;>
      rcases h₁₃ with rfl | rfl <;>
        norm_num [Int.ModEq] at hmod

end MathlibPlus.Combinatorics.QuarterTurnParity
