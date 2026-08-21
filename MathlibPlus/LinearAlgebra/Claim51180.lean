-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

namespace MathlibPlus.LinearAlgebra

open scoped BigOperators

theorem claim51180_hadamard_square :
    let H : Matrix (Fin 4) (Fin 4) ℤ :=
      !![(1 : ℤ), 1, 1, 1;
         1, 1, -1, -1;
         1, -1, 1, -1;
         1, -1, -1, 1]
    ∀ i j : Fin 4,
      (∑ k : Fin 4, H i k * H k j) = if i = j then 4 else 0 := by
  simp only
  intro i j
  fin_cases i <;> fin_cases j <;> native_decide

end MathlibPlus.LinearAlgebra
