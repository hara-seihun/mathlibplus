import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim47984

open Matrix

noncomputable section

abbrev C := ℂ
abbrev M := Matrix (Fin 2) (Fin 2) C
abbrev MR := Matrix (Fin 2) (Fin 2) ℝ

def D : M := !![Complex.I, 0; 0, -Complex.I]
def S (n : ℕ) : M := !![1, n; 0, 1]
def Sinv (n : ℕ) : M := !![1, -(n : C); 0, 1]
def Cn (n : ℕ) : M := !![Complex.I, -2 * Complex.I * n; 0, -Complex.I]
def An (n : ℕ) : MR := !![1, -2 * n; 0, -1]
def Gn (n : ℕ) : MR := !![1, -n; -n, n ^ 2 + 1]

theorem S_mul_Sinv (n : ℕ) : S n * Sinv n = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [S, Sinv, Matrix.mul_apply, Fin.sum_univ_succ]

theorem Sinv_mul_S (n : ℕ) : Sinv n * S n = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [S, Sinv, Matrix.mul_apply, Fin.sum_univ_succ]

theorem conjugate_formula (n : ℕ) : S n * D * Sinv n = Cn n := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [S, D, Sinv, Cn, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

theorem A_formula (n : ℕ) :
    (-Complex.I : C) • (Cn n) =
      (!![1, -2 * n; 0, -1] : M) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Cn, Matrix.smul_apply]
  all_goals ring_nf
  all_goals simp [Complex.I_sq, starRingEnd_apply, star_ofNat]
  all_goals ring

theorem charpoly_C (n : ℕ) : (Cn n).charpoly = Polynomial.X ^ 2 + 1 := by
  rw [Matrix.charpoly_fin_two]
  simp [Cn, Matrix.trace_fin_two, Matrix.det_fin_two]

theorem G_det (n : ℕ) : Matrix.det (Gn n) = 1 := by
  norm_num [Gn, Matrix.det_fin_two]
  ring

theorem A_preserves_G (n : ℕ) :
    (An n).transpose * Gn n * An n = Gn n := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [An, Gn, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

theorem C_isometric_for_G (n : ℕ) :
    (Cn n).conjTranspose * (Gn n).map Complex.ofReal * Cn n =
      (Gn n).map Complex.ofReal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Cn, Gn, Matrix.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp [Complex.I_sq, starRingEnd_apply, star_ofNat]
  all_goals ring

theorem G_posDef (n : ℕ) : (Gn n).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Gn, Matrix.IsHermitian, starRingEnd_apply]
  · intro x hx0
    have hx : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      have h0 : x 0 = 0 := by
        by_contra h0
        exact h (Or.inl h0)
      have h1 : x 1 = 0 := by
        by_contra h1
        exact h (Or.inr h1)
      apply hx0
      funext i
      fin_cases i <;> assumption
    simp [Gn, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
    have hform :
        x 0 * (x 0 + -(n : ℝ) * x 1) +
          x 1 * (-(n : ℝ) * x 0 + ((n : ℝ) ^ 2 + 1) * x 1) =
        (x 0 - (n : ℝ) * x 1) ^ 2 + (x 1) ^ 2 := by ring
    have hsum : 0 < (x 0 - (n : ℝ) * x 1) ^ 2 + (x 1) ^ 2 := by
      rcases hx with hx | hx
      · by_cases h1 : x 1 = 0
        · simpa [h1] using (sq_pos_of_ne_zero hx)
        · exact add_pos_of_nonneg_of_pos (sq_nonneg _)
            (sq_pos_of_ne_zero h1)
      · exact add_pos_of_nonneg_of_pos (sq_nonneg _)
          (sq_pos_of_ne_zero hx)
    nlinarith [hform]

end

end MathlibPlus.LinearAlgebra.Claim47984
