import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

namespace MathlibPlus.Combinatorics

/-- Claim 53187: the two displayed zero-based image tuples are the values
of permutations of `Fin 8`, the standard zero-based representative of
`Z/8Z`. -/
theorem exactTerminalTargetPermutations :
    ∃ (t8T7 t8T16 : Equiv.Perm (Fin 8)),
      (∀ i, t8T7 i = (![1, 6, 3, 0, 5, 2, 7, 4] : Fin 8 → Fin 8) i) ∧
        ∀ i, t8T16 i = (![1, 2, 7, 0, 5, 6, 3, 4] : Fin 8 → Fin 8) i := by
  have h7 : Function.Bijective (![1, 6, 3, 0, 5, 2, 7, 4] : Fin 8 → Fin 8) := by
    decide
  have h16 : Function.Bijective (![1, 2, 7, 0, 5, 6, 3, 4] : Fin 8 → Fin 8) := by
    decide
  exact ⟨Equiv.ofBijective _ h7, Equiv.ofBijective _ h16, by intro i; rfl, by intro i; rfl⟩

end MathlibPlus.Combinatorics
