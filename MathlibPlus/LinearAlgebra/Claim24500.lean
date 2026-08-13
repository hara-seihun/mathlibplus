import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra.Claim24500

/-- The 3-by-3 Hankel matrix from moments `m₀,…,m₄`. -/
def hankel3 (m : ℕ → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => m (i.val + j.val)

/-- A positive-definite 27-gap Hankel matrix has positive determinant. -/
theorem positive_hankel3_determinant
    (m : ℕ → ℝ) (hM : (hankel3 m).PosDef) :
    0 < (hankel3 m).det := by
  exact hM.det_pos

end MathlibPlus.LinearAlgebra.Claim24500
