import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim17394_17395R2

noncomputable section

open Matrix

/-- The first bordered determinant identity, without any positivity hypothesis. -/
theorem firstBorderedDeterminantIdentity_claim17394_r2
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : Matrix ι ι ℝ) (v : ι → ℝ) :
    N.det =
      (Matrix.fromBlocks
        (N + (1 / 4 : ℝ) • Matrix.of (fun i j => v i * v j))
        ((1 / 2 : ℝ) • (show Matrix ι (Fin 1) ℝ from fun i _ => v i))
        ((1 / 2 : ℝ) • (show Matrix (Fin 1) ι ℝ from fun _ j => v j))
        (1 : Matrix (Fin 1) (Fin 1) ℝ)).det := by
  rw [Matrix.det_fromBlocks_one₂₂]
  congr 1
  ext i j
  simp [Matrix.add_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.mul_apply,
    Fin.sum_univ_succ, Pi.smul_apply, smul_eq_mul]
  change N i j = N i j + (4⁻¹ : ℝ) * (v i * v j) -
    ((2⁻¹ : ℝ) • v i) * ((2⁻¹ : ℝ) • v j)
  simp only [smul_eq_mul]
  ring

/-- The second bordered determinant identity, without any positivity hypothesis. -/
theorem secondBorderedDeterminantIdentity_claim17395_r2
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : Matrix ι ι ℝ) (v : ι → ℝ) :
    -((N + (1 / 4 : ℝ) • Matrix.of (fun i j => v i * v j)).det) =
      (Matrix.fromBlocks N
        ((1 / 2 : ℝ) • (show Matrix ι (Fin 1) ℝ from fun i _ => v i))
        ((1 / 2 : ℝ) • (show Matrix (Fin 1) ι ℝ from fun _ j => v j))
        (-(1 : Matrix (Fin 1) (Fin 1) ℝ))).det := by
  letI : Invertible (1 : Matrix (Fin 1) (Fin 1) ℝ) := invertibleOne
  letI : Invertible (-(1 : Matrix (Fin 1) (Fin 1) ℝ)) := invertibleNeg 1
  rw [Matrix.det_fromBlocks₂₂]
  simp [Matrix.mul_apply, Fin.sum_univ_succ]
  congr 1
  ext i j
  simp [Matrix.add_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.mul_apply,
    Fin.sum_univ_succ, Pi.smul_apply, smul_eq_mul]
  change (4⁻¹ : ℝ) * (v i * v j) =
    ((2⁻¹ : ℝ) • v i) * ((2⁻¹ : ℝ) • v j)
  simp only [smul_eq_mul]
  ring

end

end MathlibPlus.LinearAlgebra.Claim17394_17395R2
