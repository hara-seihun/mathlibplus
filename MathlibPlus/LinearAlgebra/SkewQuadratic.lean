import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra.SkewQuadratic

/--
A real skew-symmetric matrix has zero quadratic form on every real vector.
The packet's parameter `c` is represented by an arbitrary finite matrix; no
additional structure on that parameter is assumed.
-/
theorem skewMatrix_quadratic_zero {n : ℕ} (Ω : Matrix (Fin n) (Fin n) ℝ)
    (hΩ : Matrix.transpose Ω = -Ω) (h : Fin n → ℝ) :
    dotProduct h (Ω.mulVec h) = 0 := by
  let q : ℝ := dotProduct h (Ω.mulVec h)
  have htranspose :
      dotProduct h ((Matrix.transpose Ω).mulVec h) = q := by
    calc
      dotProduct h ((Matrix.transpose Ω).mulVec h) =
          dotProduct h (Matrix.vecMul h Ω) := by
            rw [Matrix.mulVec_transpose]
      _ = dotProduct (Matrix.vecMul h Ω) h := dotProduct_comm _ _
      _ = q := (Matrix.dotProduct_mulVec h Ω h).symm
  have hq : q = -q := by
    calc
      q = dotProduct h ((Matrix.transpose Ω).mulVec h) := htranspose.symm
      _ = dotProduct h ((-Ω).mulVec h) := by rw [hΩ]
      _ = -q := by
        simp only [Matrix.neg_mulVec, dotProduct_neg]
        rfl
  dsimp [q] at hq ⊢
  linarith

end MathlibPlus.LinearAlgebra.SkewQuadratic
