import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace MathlibPlus.LinearAlgebra.InvariantGram


/-- The exact positive-solution part of claim 47986. -/
theorem positiveInvariantGram_solution_claim47986
    (n : ℕ) (_hn : 1 ≤ n) (x y d : ℝ)
    (hInv :
      (!![(1 : ℝ), -2 * n; 0, -1]).transpose *
          (!![x, y; y, d] : Matrix (Fin 2) (Fin 2) ℝ) *
          !![(1 : ℝ), -2 * n; 0, -1] =
        !![x, y; y, d])
    (hPos : (!![x, y; y, d] : Matrix (Fin 2) (Fin 2) ℝ).PosDef) :
    y = -(n : ℝ) * x ∧ d > (n : ℝ) ^ 2 * x := by
  have h01 := congrFun (congrFun hInv 0) 1
  have hy : -(x * (2 * (n : ℝ))) + -y = y := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h01
  have hy' : y = -(n : ℝ) * x := by
    nlinarith [hy]
  have hx : 0 < x := by
    have h := hPos.dotProduct_mulVec_pos
      (x := ![(1 : ℝ), 0]) (by norm_num)
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two] using h
  have hd : 0 < d - (n : ℝ) ^ 2 * x := by
    have h := hPos.dotProduct_mulVec_pos
      (x := ![(n : ℝ), 1]) (by norm_num)
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hy'] at h
    nlinarith [h]
  exact ⟨hy', by linarith⟩

/-- The uniform-boundedness consequence of claim 47986.  The two
`PosSemidef` hypotheses are the coordinate form of `m I ≤ G_n ≤ M I` for
these symmetric two-by-two matrices. -/
theorem no_uniform_coercive_gram_family_claim47986
    (m M : ℝ) (hm : 0 < m) (hmM : m ≤ M)
    (x y d : ℕ → ℝ)
    (hInv : ∀ n : ℕ, 1 ≤ n →
      (!![(1 : ℝ), -2 * n; 0, -1]).transpose *
          (!![x n, y n; y n, d n] : Matrix (Fin 2) (Fin 2) ℝ) *
          !![(1 : ℝ), -2 * n; 0, -1] =
        !![x n, y n; y n, d n])
    (hPos : ∀ n : ℕ, 1 ≤ n →
      (!![x n, y n; y n, d n] : Matrix (Fin 2) (Fin 2) ℝ).PosDef)
    (hLower : ∀ n : ℕ, 1 ≤ n →
      (!![x n - m, y n; y n, d n - m] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef)
    (hUpper : ∀ n : ℕ, 1 ≤ n →
      (!![M - x n, -y n; -y n, M - d n] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef) :
    False := by
  have hratio : 1 ≤ M / m := by
    exact (le_div_iff₀ hm).2 (by simpa [one_mul] using hmM)
  obtain ⟨N, hN⟩ := exists_nat_gt (M / m + 1)
  have hNreal : M / m + 1 < (N : ℝ) := by exact_mod_cast hN
  have hNone : 1 < (N : ℝ) := by linarith
  have hNm : M < (N : ℝ) * m := by
    apply (div_lt_iff₀ hm).mp
    linarith
  have hNN : (N : ℝ) ≤ (N : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((N : ℝ) - 1)]
  have hN2m : (N : ℝ) * m ≤ (N : ℝ) ^ 2 * m := by
    exact mul_le_mul_of_nonneg_right hNN hm.le
  have hMlt : M < (N : ℝ) ^ 2 * m := lt_of_lt_of_le hNm hN2m
  have hNle : 1 ≤ N := by
    exact Nat.le_of_lt (by exact_mod_cast hNone)
  have hx_lower : m ≤ x N := by
    have h := (hLower N hNle).diag_nonneg (i := 0)
    simpa using (show 0 ≤ x N - m from h)
  have hd_upper : d N ≤ M := by
    have h := (hUpper N hNle).diag_nonneg (i := 1)
    simpa using (show 0 ≤ M - d N from h)
  have hsol := positiveInvariantGram_solution_claim47986
    N hNle (x N) (y N) (d N) (hInv N hNle) (hPos N hNle)
  have hxm : (N : ℝ) ^ 2 * m ≤ (N : ℝ) ^ 2 * x N :=
    mul_le_mul_of_nonneg_left hx_lower (sq_nonneg _)
  have hMd : M < d N :=
    lt_of_lt_of_le hMlt hxm |>.trans hsol.2
  exact (not_lt_of_ge hd_upper) hMd

end MathlibPlus.LinearAlgebra.InvariantGram
