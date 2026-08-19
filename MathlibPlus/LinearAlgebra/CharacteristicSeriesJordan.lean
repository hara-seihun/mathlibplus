import Mathlib

open Matrix

namespace MathlibPlus.LinearAlgebra

/-- The characteristic series and all power traces do not detect the displayed
Jordan extension. -/
theorem characteristicSeries_forgetsJordanExtension_claim11089 :
    let A : Matrix (Fin 2) (Fin 2) ℚ := !![3, 0; 0, 3]
    let B : Matrix (Fin 2) (Fin 2) ℚ := !![3, 1; 0, 3]
    let Ap : Matrix (Fin 2) (Fin 2) (Polynomial ℚ) := !![3, 0; 0, 3]
    let Bp : Matrix (Fin 2) (Fin 2) (Polynomial ℚ) := !![3, 1; 0, 3]
    let T : Polynomial ℚ := Polynomial.X
    Matrix.det (1 - T • Ap) = (1 - 3 * T) ^ 2 ∧
      Matrix.det (1 - T • Bp) = (1 - 3 * T) ^ 2 ∧
      (∀ n : ℕ,
        Matrix.trace (A ^ n) = 2 * (3 : ℚ) ^ n ∧
          Matrix.trace (B ^ n) = 2 * (3 : ℚ) ^ n) ∧
      Matrix.rank (A - (3 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ)) = 0 ∧
      Matrix.rank (B - (3 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ)) = 1 := by
  dsimp
  constructor
  · rw [Matrix.det_fin_two]
    simp
    ring
  constructor
  · rw [Matrix.det_fin_two]
    simp
    ring
  constructor
  · intro n
    have hA : ∀ n : ℕ, (!![3, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℚ) ^ n =
        !![(3 : ℚ)^n, 0; 0, 3^n] := by
      intro n
      induction n with
      | zero =>
        ext i j
        fin_cases i <;> fin_cases j <;> norm_num
      | succ n ih =>
        rw [pow_succ, ih]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]
    have hB : ∀ n : ℕ, ∃ c : ℚ,
        (!![3, 1; 0, 3] : Matrix (Fin 2) (Fin 2) ℚ) ^ n =
          !![(3 : ℚ)^n, c; 0, 3^n] := by
      intro n
      induction n with
      | zero =>
        refine ⟨0, ?_⟩
        ext i j
        fin_cases i <;> fin_cases j <;> norm_num
      | succ n ih =>
        obtain ⟨c, hc⟩ := ih
        refine ⟨(3 : ℚ)^n + 3*c, ?_⟩
        rw [pow_succ, hc]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]
          <;> ring
    obtain ⟨c, hc⟩ := hB n
    rw [hA n, hc]
    simp [Matrix.trace_fin_two]
    ring
  constructor
  · have hzero :
        (!![3, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℚ) -
            (3 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ) = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
          Pi.smul_apply, smul_eq_mul]
    rw [hzero]
    exact Matrix.rank_zero
  · let M : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 0, 0]
    have hM :
        (!![3, 1; 0, 3] : Matrix (Fin 2) (Fin 2) ℚ) -
            (3 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ) = M := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [M, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
          Pi.smul_apply, smul_eq_mul]
    rw [hM, Matrix.rank_eq_finrank_span_cols]
    have hcol0 : M.col 0 = 0 := by
      funext i
      fin_cases i <;> rfl
    have hcol1 : M.col 1 = ![1, 0] := by
      funext i
      fin_cases i <;> rfl
    have hspan : Submodule.span ℚ (Set.range M.col) = ℚ ∙ ![1, 0] := by
      apply le_antisymm
      · refine Submodule.span_le.2 ?_
        rintro v ⟨j, rfl⟩
        fin_cases j
        · change M.col (0 : Fin 2) ∈ ℚ ∙ ![1, 0]
          rw [hcol0]
          exact Submodule.zero_mem _
        · change M.col (1 : Fin 2) ∈ ℚ ∙ ![1, 0]
          rw [hcol1]
          exact Submodule.mem_span_singleton_self _
      · refine Submodule.span_mono ?_
        rintro v rfl
        rw [← hcol1]
        exact Set.mem_range.mpr ⟨(1 : Fin 2), rfl⟩
    rw [hspan]
    apply finrank_span_singleton
    decide

end MathlibPlus.LinearAlgebra
