import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim10392

open Matrix

/-- Characteristic polynomial of the displayed Frobenius matrix. -/
theorem frobenius_charpoly_claim10392 :
    (let F : Matrix (Fin 2) (Fin 2) ℤ := !![0, -5; 1, -3]
     F.charpoly = Polynomial.X ^ 2 + Polynomial.C (3 : ℤ) * Polynomial.X + Polynomial.C 5) := by
  dsimp
  rw [Matrix.charpoly_fin_two]
  simp [Matrix.trace, Matrix.det_fin_two, Fin.sum_univ_two]

/-- The displayed matrix has `det (I - F) = 9` over characteristic zero. -/
theorem det_one_sub_frobenius_claim10392 :
    (let F : Matrix (Fin 2) (Fin 2) ℚ := !![0, -5; 1, -3]
     (1 - F).det = (9 : ℚ)) := by
  dsimp
  simp [Matrix.det_fin_two]
  norm_num

/-- The suspension map `I-F` has trivial kernel in the displayed rational
model. -/
theorem kernel_one_sub_frobenius_claim10392 :
    ∀ v : Fin 2 → ℚ,
      (1 - !![0, -5; 1, -3] : Matrix (Fin 2) (Fin 2) ℚ) *ᵥ v = 0 → v = 0 := by
  intro v h
  let M : Matrix (Fin 2) (Fin 2) ℚ := !![1, 5; -1, 4]
  have hM : (1 - !![0, -5; 1, -3] : Matrix (Fin 2) (Fin 2) ℚ) = M := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [M]
  rw [hM] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [M, Matrix.mulVec, Matrix.mul_apply, Fin.sum_univ_two] at h0 h1
  change v 0 + 5 * v 1 = 0 at h0
  change -v 0 + 4 * v 1 = 0 at h1
  have hv0 : v 0 = 0 := by linarith [h0, h1]
  have hv1 : v 1 = 0 := by linarith [h0, h1]
  funext i
  fin_cases i
  · exact hv0
  · exact hv1

/-- The same displayed suspension map is surjective in the rational model,
so its cokernel is trivial. -/
theorem surjective_one_sub_frobenius_claim10392 :
    ∀ v : Fin 2 → ℚ, ∃ w : Fin 2 → ℚ,
      (1 - !![0, -5; 1, -3] : Matrix (Fin 2) (Fin 2) ℚ) *ᵥ w = v := by
  intro v
  let M : Matrix (Fin 2) (Fin 2) ℚ := !![1, 5; -1, 4]
  have hM : (1 - !![0, -5; 1, -3] : Matrix (Fin 2) (Fin 2) ℚ) = M := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [M]
  rw [hM]
  refine ⟨![ (4 * v 0 - 5 * v 1) / 9, (v 0 + v 1) / 9 ], ?_⟩
  have hv0 : (M *ᵥ ![ (4 * v 0 - 5 * v 1) / 9, (v 0 + v 1) / 9 ]) 0 = v 0 := by
    simp [M, Matrix.mulVec, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have hv1 : (M *ᵥ ![ (4 * v 0 - 5 * v 1) / 9, (v 0 + v 1) / 9 ]) 1 = v 1 := by
    simp [M, Matrix.mulVec, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  funext i
  fin_cases i
  · exact hv0
  · exact hv1

/-- The two-dimensional carrier used by the displayed matrix witness has the
claimed dimension. -/
theorem two_dimensional_carrier_claim10392 :
    Module.finrank ℚ (Fin 2 → ℚ) = 2 := by
  simp

end MathlibPlus.LinearAlgebra.Claim10392
