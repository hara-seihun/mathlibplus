import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- The local matrix core of admitted claim 39905.  In an adapted basis, the
upper-right entry of a relative upper-triangular matrix is a nonzero diagonal
scalar times the difference of the two shear coordinates. -/
theorem relativeUpperTriangularShear
    {K : Type*} [Field K]
    (a d a' d' c c' : K)
    (ha : a ≠ 0) (hd : d ≠ 0) (_ha' : a' ≠ 0) (hd' : d' ≠ 0) :
    let L : Matrix (Fin 2) (Fin 2) K := !![a, c * d; 0, d]
    let Linv : Matrix (Fin 2) (Fin 2) K :=
      !![a⁻¹, -a⁻¹ * c; 0, d⁻¹]
    let L' : Matrix (Fin 2) (Fin 2) K := !![a', c' * d'; 0, d']
    Linv * L = 1 ∧
      (Linv * L') 0 1 = a⁻¹ * d' * (c' - c) ∧
      ((Linv * L') 0 1 ≠ 0 ↔ c' ≠ c) := by
  dsimp
  have hentry :
      ((!![a⁻¹, -a⁻¹ * c; 0, d⁻¹] : Matrix (Fin 2) (Fin 2) K) *
        !![a', c' * d'; 0, d']) 0 1 = a⁻¹ * d' * (c' - c) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hd] <;> ring
  constructor
  · exact hentry
  · rw [hentry]
    constructor
    · intro h hEq
      apply h
      simp [hEq]
    · intro h
      exact mul_ne_zero (mul_ne_zero (inv_ne_zero ha) (by exact hd'))
        (sub_ne_zero.mpr h)

end MathlibPlus.LinearAlgebra
