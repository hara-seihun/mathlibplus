import Mathlib

namespace MathlibPlus.LinearAlgebra.ConformalSymplecticGamma

/-!
# Conformal symplectic identity for the gamma transfer matrix

Claim 17538 is formalized over an arbitrary commutative ring. The parameter
`z` is retained explicitly and `a z` is the scalar appearing in the displayed
matrix.
-/

/-- For `A(z) = [[0, 1], [a(z), 0]]` and `J = [[0, 1], [-1, 0]]`,
`A(z)ᵀ J A(z) = -a(z) J`. -/
theorem conformalSymplecticGammaTransfer {Z R : Type*} [CommRing R]
    (a : Z → R) (z : Z) :
    let A : Matrix (Fin 2) (Fin 2) R := !![0, 1; a z, 0]
    let J : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, 0]
    A.transpose * J * A = -(a z) • J := by
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

end MathlibPlus.LinearAlgebra.ConformalSymplecticGamma
