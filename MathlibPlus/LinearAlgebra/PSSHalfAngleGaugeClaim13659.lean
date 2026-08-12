import Mathlib

open scoped Matrix

namespace MathlibPlus.LinearAlgebra

/-- Claim 13659, with the packet's two matrix displays kept local so that the
formalization introduces no unreviewed public definition. -/
theorem pssHalfAngleGauge_claim13659 (t : ℝ) :
    let θ := t * Real.log 2
    let P : Matrix (Fin 2) (Fin 2) ℂ :=
      !![Complex.exp (Complex.I * (θ : ℂ) / 2), 0;
         0, Complex.exp (-Complex.I * (θ : ℂ) / 2)]
    let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
    let H : Matrix (Fin 2) (Fin 2) ℂ :=
      (1 / Real.sqrt 2 : ℂ) • !![1, 1; 1, -1]
    let C := P * X * Matrix.conjTranspose P
    let U := P * H
    C = !![0, Complex.exp (Complex.I * (θ : ℂ));
            Complex.exp (-Complex.I * (θ : ℂ)), 0] ∧
      U = P * H := by
  dsimp
  constructor
  · ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose]
    · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose]
      rw [← Complex.exp_conj, ← Complex.exp_add]
      congr 1
      rw [map_div₀, map_neg, map_mul]
      have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat (starRingEnd ℂ) 2
      rw [htwo]
      have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
        symm
        exact Complex.ofReal_log (by norm_num)
      rw [hlog]
      simp only [Complex.conj_I, Complex.conj_ofReal, map_mul] <;> ring
    · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose]
      rw [← Complex.exp_conj, ← Complex.exp_add]
      congr 1
      rw [map_div₀, map_mul]
      have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat (starRingEnd ℂ) 2
      rw [htwo]
      have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
        symm
        exact Complex.ofReal_log (by norm_num)
      rw [hlog]
      simp only [Complex.conj_I, Complex.conj_ofReal, map_mul] <;> ring
    · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose]
  · rfl

end MathlibPlus.LinearAlgebra
