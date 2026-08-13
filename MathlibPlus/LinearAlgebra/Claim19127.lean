import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra.Claim19127

/--
The global Schur complement is homogeneous of degree one under a positive
scalar.  The determinant-unit hypothesis is the exact invertibility condition
needed for the displayed inverse; no positivity of the surrounding block is
needed for this algebraic identity.
-/
theorem globalSchurComplementHomogeneous_claim19127
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (scale : ℝ) (hscale : 0 < scale) (hD : IsUnit D.det) :
    (scale : ℂ) • (A - B * D⁻¹ * B.conjTranspose) =
      ((scale : ℂ) • A) - ((scale : ℂ) • B) * ((scale : ℂ) • D)⁻¹ *
        ((scale : ℂ) • B).conjTranspose := by
  have hscale0 : (scale : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hscale
  letI : Invertible (scale : ℂ) := invertibleOfNonzero hscale0
  rw [Matrix.inv_smul D (scale : ℂ) hD]
  simp only [Matrix.conjTranspose_smul]
  simp only [smul_sub, Matrix.smul_mul, Matrix.mul_smul]
  simp only [invOf_eq_inv]
  field_simp
  simp [smul_smul, hscale0]

end MathlibPlus.LinearAlgebra.Claim19127
