import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim19395

/-- The two displayed rank-one/sign-twisted 2-by-2 matrices have the same
trace, namely `2 * q`. -/
theorem canonicalRankTwo_equalTraces_claim19395 (q : ℝ) :
    let E : Matrix (Fin 2) (Fin 2) ℝ := !![q, q; q, q]
    let O : Matrix (Fin 2) (Fin 2) ℝ := !![q, -q; -q, q]
    Matrix.trace E = 2 * q ∧ Matrix.trace O = 2 * q ∧
      Matrix.trace E = Matrix.trace O := by
  dsimp
  norm_num [Matrix.trace, Fin.sum_univ_succ]
  ring

end MathlibPlus.LinearAlgebra.Claim19395
