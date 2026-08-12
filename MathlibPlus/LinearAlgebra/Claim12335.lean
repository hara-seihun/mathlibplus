import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim12335

/-- The two displayed matrix families have the same determinant polynomial, but
 their zero fibres have different kernels.  The square-zero, nonzero Jordan
 block records the asserted length-two nilpotent structure. -/
theorem determinantDoesNotDetermineZeroFiberMultiplicity {K : Type*} [Field K] :
    let D : K → Matrix (Fin 2) (Fin 2) K := fun t => !![t, 0; 0, t]
    let J : K → Matrix (Fin 2) (Fin 2) K := fun t => !![t, 1; 0, t]
    (∀ t, Matrix.det (D t) = t ^ 2 ∧ Matrix.det (J t) = t ^ 2) ∧
      (∀ x : Fin 2 → K, Matrix.mulVec (D 0) x = 0) ∧
      (∀ x : Fin 2 → K, Matrix.mulVec (J 0) x = 0 ↔ x 1 = 0) ∧
      (J 0 ≠ 0) ∧
      (J 0 * J 0 = 0) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t
    constructor <;> rw [Matrix.det_fin_two] <;> simp <;> ring
  · intro x
    funext i
    fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · intro x
    constructor
    · intro h
      have h0 := congr_fun h 0
      have h1 := congr_fun h 1
      norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
      exact h0
    · intro hx
      funext i
      fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hx]
  · intro h
    have := congr_fun (congr_fun h 0) 1
    simp at this
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, dotProduct]

end MathlibPlus.LinearAlgebra.Claim12335
