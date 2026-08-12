import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace MathlibPlus.Algebra.Claim48021

/-- The exact three altered log-concavity slacks recorded in claim 48021.
The `gᵢ` are the coefficient formulas supplied by the packet's broom
construction; this theorem does not assert the surrounding real-rootedness
or forest-closure claims. -/
theorem alteredLogConcavitySlacks_48021 (r : ℕ) :
    let q : ℚ := r
    let g₀ : ℚ := 1
    let g₁ : ℚ := q + 4
    let g₂ : ℚ := (q + 2) * (q + 3) / 2
    let g₃ : ℚ := q * (q ^ 2 + 6 * q - 1) / 6
    let g₄ : ℚ := q * (q - 1) * (q ^ 2 + 7 * q - 6) / 24
    (g₁ ^ 2 - g₀ * g₂ = (q ^ 2 + 11 * q + 26) / 2 ∧
      0 < (q ^ 2 + 11 * q + 26) / 2) ∧
    (g₂ ^ 2 - g₁ * g₃ =
        (q ^ 4 + 10 * q ^ 3 + 65 * q ^ 2 + 188 * q + 108) / 12 ∧
      0 < (q ^ 4 + 10 * q ^ 3 + 65 * q ^ 2 + 188 * q + 108) / 12) ∧
    (g₃ ^ 2 - g₂ * g₄ =
        q * (q ^ 5 + 15 * q ^ 4 + 67 * q ^ 3 + 21 * q ^ 2 + 148 * q - 108) / 144 ∧
      0 ≤ q * (q ^ 5 + 15 * q ^ 4 + 67 * q ^ 3 + 21 * q ^ 2 + 148 * q - 108) / 144) := by
  dsimp
  have hq : 0 ≤ (r : ℚ) := by exact_mod_cast (Nat.zero_le r)
  have hq1 : 1 ≤ (r : ℚ) ∨ r = 0 := by
    rcases r with _ | r
    · exact Or.inr rfl
    · exact Or.inl (by exact_mod_cast r.succ_pos)
  constructor
  · constructor
    · ring
    · nlinarith [sq_nonneg (r : ℚ)]
  constructor
  · constructor
    · ring
    · nlinarith [sq_nonneg ((r : ℚ) ^ 2), sq_nonneg ((r : ℚ) ^ 2 + 5 * (r : ℚ))]
  · constructor
    · ring
    · rcases hq1 with hq1 | rzero
      · have hlinear : 0 ≤ 148 * (r : ℚ) - 108 := by nlinarith
        nlinarith [sq_nonneg ((r : ℚ) ^ 2), sq_nonneg ((r : ℚ) ^ 3),
          sq_nonneg ((r : ℚ) ^ 4), sq_nonneg ((r : ℚ) ^ 5)]
      · simp [rzero]

end MathlibPlus.Algebra.Claim48021
