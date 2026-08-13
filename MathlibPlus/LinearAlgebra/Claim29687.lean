import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim29687

/-- The entrywise gain of commuting a diagonal observable through a matrix. -/
theorem diagonalObservableMotifGain {n : ℕ} {R : Type*} [CommRing R]
    (K : Matrix (Fin n) (Fin n) R) (h : Fin n → R) (s u : Fin n) :
    (K * Matrix.diagonal h - Matrix.diagonal h * K) s u =
      (h u - h s) * K s u := by
  change (K * Matrix.diagonal h) s u - (Matrix.diagonal h * K) s u = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

end MathlibPlus.LinearAlgebra.Claim29687
