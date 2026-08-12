import Mathlib

namespace MathlibPlus.Combinatorics.Claim30396

/-- The exact table and direction/profile counts in the finite residual census. -/
theorem alignedDirectionProfileCardinality :
    Fintype.card (Fin 3 → Fin 3) = 27 ∧
      Fintype.card {t : Fin 3 → Fin 3 // t ≠ 0} = 26 ∧
      Fintype.card (Fin 4 × {t : Fin 3 → Fin 3 // t ≠ 0}) = 104 := by
  decide

end MathlibPlus.Combinatorics.Claim30396
