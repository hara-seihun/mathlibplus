import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- Claim 25580: the explicit context matrix is lower unitriangular and has
unit determinant. -/
theorem claim25580_contextMatrix_lowerUnitriangular {R : Type*} [CommRing R]
    (D B Q : R) :
    let U : Matrix (Fin 4) (Fin 4) R :=
      !![1, 0, 0, 0;
         D, 1, 0, 0;
         B, D, 1, 0;
         Q, 0, 0, 1]
    (U.IsLowerTriangular ∧ (∀ i, U i i = 1) ∧ U.det = 1) := by
  dsimp
  let U : Matrix (Fin 4) (Fin 4) R :=
    !![1, 0, 0, 0;
       D, 1, 0, 0;
       B, D, 1, 0;
       Q, 0, 0, 1]
  have htri : U.IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    fin_cases i <;> fin_cases j <;> simp_all [U]
  have hdiag : ∀ i, U i i = 1 := by
    intro i
    fin_cases i <;> simp [U]
  have hdet : U.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular U htri]
    simp [hdiag]
  exact ⟨htri, hdiag, hdet⟩

end MathlibPlus.LinearAlgebra
