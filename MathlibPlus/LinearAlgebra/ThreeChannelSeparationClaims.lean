import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MathlibPlus.LinearAlgebra

/-- The coefficient-matrix certificate for claim 14743.  The source's preceding
claim fixes `d = 2 + x > 0`; the extracted statement also uses either heat sign. -/
theorem threeSeparateChannels_dimension_minimal_claim14743
    (x lam g σ : ℝ)
    (hx : 0 < 2 + x)
    (hσ : σ = 1 ∨ σ = -1)
    (hκ : lam * g ≠ 0) :
    let d : ℝ := 2 + x
    let κ : ℝ := lam * g
    let M : Matrix (Fin 3) (Fin 3) ℝ :=
      !![0, -2, 0; d, 0, 0; 0, 0, σ * κ]
    let R : ℝ → ℝ → ℝ := fun U Φ =>
      d * Real.cosh U - 2 * Real.cos Φ + σ * κ * Real.sinh U * Real.sin Φ
    (∀ U Φ : ℝ,
        R U Φ = d * Real.cosh U + (-2) * Real.cos Φ +
          (σ * κ * Real.sinh U) * Real.sin Φ) ∧
      Matrix.det M = 2 * σ * d * κ ∧
      Matrix.det M ≠ 0 ∧
      ¬ ∃ (L : Matrix (Fin 3) (Fin 2) ℝ)
          (B : Matrix (Fin 2) (Fin 2) ℝ)
          (Rmat : Matrix (Fin 2) (Fin 3) ℝ),
        M = L * B * Rmat := by
  dsimp
  have hσ0 : σ ≠ 0 := by
    rcases hσ with rfl | rfl <;> norm_num
  have hd : 2 + x ≠ 0 := ne_of_gt hx
  have hdet :
      Matrix.det (!![0, -2, 0; 2 + x, 0, 0; 0, 0, σ * (lam * g)] :
        Matrix (Fin 3) (Fin 3) ℝ) =
        2 * σ * (2 + x) * (lam * g) := by
    simp [Matrix.det_fin_three]
    ring
  have hprod : 2 * σ * (2 + x) * (lam * g) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hσ0) hd) hκ
  refine ⟨?_, hdet, ?_, ?_⟩
  · intro U Φ
    ring
  · rw [hdet]
    exact hprod
  · intro hfactor
    have hdet_zero :
        Matrix.det (!![0, -2, 0; 2 + x, 0, 0; 0, 0, σ * (lam * g)] :
          Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
      rcases hfactor with ⟨L, B, Rmat, hfactor⟩
      rw [hfactor]
      simp [Matrix.det_fin_three, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    rw [hdet] at hdet_zero
    exact hprod hdet_zero

end MathlibPlus.LinearAlgebra
