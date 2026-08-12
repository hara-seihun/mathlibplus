import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- Claim 11057: the displayed rank-two companion matrix is symplectic, and its
quadratic denominator has the displayed coefficients. -/
theorem rankTwoCompanionSymplecticAndDeterminant :
    ∀ a u : ℝ,
      let A : Matrix (Fin 2) (Fin 2) ℝ := !![(0 : ℝ), -1; 1, a]
      let J : Matrix (Fin 2) (Fin 2) ℝ := !![(0 : ℝ), 1; -1, 0]
      A.transpose * J * A = J ∧
        (1 - u • A).det = 1 - a * u + u ^ 2 := by
  intro a u
  dsimp
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [Matrix.det_fin_two]
    norm_num
    ring

end MathlibPlus.LinearAlgebra
