import Mathlib

namespace MathlibPlus.Combinatorics.Claim51728

/-- The exact stars-and-bars count for multisets of five elements from a
48-element type. -/
theorem unorderedMultisetsOfFiveFrom48_claim51728 :
    Fintype.card (Sym (Fin 48) 5) = 2598960 := by
  rw [Sym.card_sym_eq_choose]
  norm_num [Nat.choose]

end MathlibPlus.Combinatorics.Claim51728
