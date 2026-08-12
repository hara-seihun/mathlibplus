import Mathlib

namespace MathlibPlus.Combinatorics

/-! Formalization of admitted claim 32696. -/

/-- The twelve-coordinate profiles over a fixed five-symbol alphabet number `5^12`.

The function type makes the twelve coordinates and five available symbols explicit.
-/
theorem rawFixedAlphabetProfileCount :
    Fintype.card (Fin 12 → Fin 5) = 5 ^ 12 ∧
      5 ^ 12 = 244140625 := by
  rw [Fintype.card_fun]
  norm_num

end MathlibPlus.Combinatorics
