import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim36714Transport

/-!
Formalization of the explicit matrix and boundary-vector identities in admitted
claim 36714.  The source's geometric names for cells are not needed for these
literal integer identities.
-/

/-- The three displayed transport matrices satisfy `Σ ∂ₙ = ∂ₘ`. -/
theorem commutingTransportMatrices_36714 :
    let dn : Matrix (Fin 3) (Fin 2) ℤ := !![1, 0; -1, 1; 0, -1]
    let sigma : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 1, 1, 0; 0, 1, 2]
    let dm : Matrix (Fin 3) (Fin 2) ℤ := !![1, 0; 0, 1; -1, -1]
    sigma * dn = dm := by
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

/-- The two adjacent top boundary vectors telescope to the endpoint boundary. -/
theorem topBoundaryTelescope_36714 :
    let first : Fin 3 → ℤ := ![1, -1, 0]
    let second : Fin 3 → ℤ := ![0, 1, -1]
    let total : Fin 3 → ℤ := ![1, 0, -1]
    first + second = total := by
  dsimp
  funext i
  fin_cases i <;> norm_num

end MathlibPlus.LinearAlgebra.Claim36714Transport
