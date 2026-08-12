import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim12290

/--
The exact integer matrix witness from claim 12290 satisfies the displayed
alternating-form similitude and has the displayed characteristic polynomial.
The approximate eigenvalue moduli and the source's purity terminology are left
outside this algebraic core because they are not exact Lean data in the claim.
-/
theorem offPurityFrobeniusWitness_claim12290 :
    let Ffake : Matrix (Fin 2) (Fin 2) ℤ := !![0, -9; 1, -7]
    let J : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]
    Ffake.transpose * J * Ffake = 9 • J ∧
      Ffake.charpoly = Polynomial.X ^ 2 + 7 * Polynomial.X + 9 := by
  dsimp
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [Matrix.charpoly_fin_two]
    norm_num

end MathlibPlus.LinearAlgebra.Claim12290
