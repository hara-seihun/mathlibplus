import Mathlib

namespace MathlibPlus.Algebra.Claim17588

open Matrix
open NormedSpace

/-- A square-zero real matrix has the expected finite exponential series. -/
lemma exp_smul_of_square_zero {𝕜 : Type*} [NormedField 𝕜] [CharZero 𝕜]
    [CompleteSpace 𝕜]
    {A : Matrix (Fin 2) (Fin 2) 𝕜} (hA : A ^ 2 = 0) (a : 𝕜) :
    exp (a • A) = 1 + a • A := by
  have hpow : ∀ n : ℕ, 2 ≤ n → A ^ n = 0 := by
    intro n hn
    calc
      A ^ n = A ^ (n - 2 + 2) := by congr 1 <;> omega
      _ = A ^ (n - 2) * A ^ 2 := by rw [pow_add]
      _ = 0 := by rw [hA, mul_zero]
  rw [NormedSpace.exp_eq_tsum 𝕜]
  change (∑' n : ℕ, (n.factorial : 𝕜)⁻¹ • (a • A) ^ n) = 1 + a • A
  rw [tsum_eq_sum (s := Finset.range 2)]
  · norm_num [Finset.sum_range_succ, smul_pow]
  · intro n hn
    have hn2 : 2 ≤ n := by
      have : ¬ n < 2 := by simpa [Finset.mem_range] using hn
      omega
    simp [smul_pow, hpow n hn2]

/-- Claim 17588 over a complete normed characteristic-zero field. -/
theorem nilpotent_shear_exponentials {𝕜 : Type*} [NormedField 𝕜] [CharZero 𝕜]
    [CompleteSpace 𝕜] (a b : 𝕜) :
    let E : Matrix (Fin 2) (Fin 2) 𝕜 := !![0, 1; 0, 0]
    let F : Matrix (Fin 2) (Fin 2) 𝕜 := !![0, 0; 1, 0]
    E ^ 2 = 0 ∧ F ^ 2 = 0 ∧
      exp (a • E) = !![1, a; 0, 1] ∧
      exp (b • F) = !![1, 0; b, 1] := by
  dsimp
  have hE : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) 𝕜) ^ 2 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  have hF : (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) 𝕜) ^ 2 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨hE, hF, ?_, ?_⟩
  · change exp (a • (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) 𝕜)) = !![1, a; 0, 1]
    rw [exp_smul_of_square_zero hE]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.add_apply, Matrix.smul_apply]
  · change exp (b • (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) 𝕜)) = !![1, 0; b, 1]
    rw [exp_smul_of_square_zero hF]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.add_apply, Matrix.smul_apply]

end MathlibPlus.Algebra.Claim17588
