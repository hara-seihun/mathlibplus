import Mathlib

open Polynomial

namespace MathlibPlus.LinearAlgebra

/-- The displayed semisimple and Jordan matrices have the same repeated-root
spectral and trace data, but their shifted nilpotent parts differ.  The final
conjugacy clause is the explicit matrix-level form of the operator-module
separation in the claim. -/
theorem semisimple_and_jordan_repeated_root_claim10404 :
    let F : Matrix (Fin 2) (Fin 2) ℝ := !![(-3 : ℝ), 0; 0, -3]
    let J : Matrix (Fin 2) (Fin 2) ℝ := !![(-3 : ℝ), 1; 0, -3]
    F.charpoly = (X - C (-3 : ℝ)) ^ 2 ∧
      J.charpoly = (X - C (-3 : ℝ)) ^ 2 ∧
      (∀ k : ℕ, 1 ≤ k →
        Matrix.trace (F ^ k) = 2 * (-3 : ℝ) ^ k ∧
        Matrix.trace (J ^ k) = 2 * (-3 : ℝ) ^ k) ∧
      F + (3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) = 0 ∧
      J + (3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 ∧
      (J + (3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ^ 2 = 0 ∧
      ¬ ∃ P Q : Matrix (Fin 2) (Fin 2) ℝ,
        P * Q = 1 ∧ Q * P = 1 ∧ Q * F * P = J := by
  let F : Matrix (Fin 2) (Fin 2) ℝ := !![(-3 : ℝ), 0; 0, -3]
  let J : Matrix (Fin 2) (Fin 2) ℝ := !![(-3 : ℝ), 1; 0, -3]
  change F.charpoly = (X - C (-3 : ℝ)) ^ 2 ∧
      J.charpoly = (X - C (-3 : ℝ)) ^ 2 ∧
      (∀ k : ℕ, 1 ≤ k →
        Matrix.trace (F ^ k) = 2 * (-3 : ℝ) ^ k ∧
        Matrix.trace (J ^ k) = 2 * (-3 : ℝ) ^ k) ∧
      F + (3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) = 0 ∧
      J + (3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 ∧
      (J + (3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ^ 2 = 0 ∧
      ¬ ∃ P Q : Matrix (Fin 2) (Fin 2) ℝ,
        P * Q = 1 ∧ Q * P = 1 ∧ Q * F * P = J
  have hcharF : F.charpoly = (X - C (-3 : ℝ)) ^ 2 := by
    rw [Matrix.charpoly_fin_two]
    dsimp [F]
    simp [Matrix.trace_fin_two, Matrix.det_fin_two]
    ring
  have hcharJ : J.charpoly = (X - C (-3 : ℝ)) ^ 2 := by
    rw [Matrix.charpoly_fin_two]
    dsimp [J]
    simp [Matrix.trace_fin_two, Matrix.det_fin_two]
    ring
  have hFpow : ∀ k : ℕ, F ^ k = !![(-3 : ℝ) ^ k, 0; 0, (-3 : ℝ) ^ k] := by
    intro k
    induction k with
    | zero =>
        simp only [pow_zero]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
    | succ k ih =>
        rw [pow_succ, ih]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [F, Matrix.mul_apply, Fin.sum_univ_two, pow_succ]
  have hJpow : ∀ k : ℕ, ∃ u : ℝ,
      J ^ k = !![(-3 : ℝ) ^ k, u; 0, (-3 : ℝ) ^ k] := by
    intro k
    induction k with
    | zero =>
        refine ⟨0, ?_⟩
        simp only [pow_zero]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
    | succ k ih =>
        obtain ⟨u, hu⟩ := ih
        refine ⟨u * (-3) + (-3 : ℝ) ^ k, ?_⟩
        rw [pow_succ, hu]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [J, Matrix.mul_apply, Fin.sum_univ_two, pow_succ]
        ring
  have htrace : ∀ k : ℕ,
      Matrix.trace (F ^ k) = 2 * (-3 : ℝ) ^ k ∧
      Matrix.trace (J ^ k) = 2 * (-3 : ℝ) ^ k := by
    intro k
    constructor
    · rw [hFpow k]
      simp [Matrix.trace_fin_two]
      ring
    · obtain ⟨u, hu⟩ := hJpow k
      rw [hu]
      simp [Matrix.trace_fin_two]
      ring
  have htrace_pos : ∀ k : ℕ, 1 ≤ k →
      Matrix.trace (F ^ k) = 2 * (-3 : ℝ) ^ k ∧
      Matrix.trace (J ^ k) = 2 * (-3 : ℝ) ^ k := by
    intro k hk
    exact htrace k
  have hFzero :
      F + (3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [F]
  have hshift :
      J + (3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) =
        !![(0 : ℝ), 1; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J]
  have hJnonzero :
      J + (3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 := by
    rw [hshift]
    intro h
    have hentry := congrFun (congrFun h 0) 1
    norm_num at hentry
  have hJnil :
      (J + (3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ^ 2 = 0 := by
    rw [hshift]
    simp only [pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hFscalar :
      F = (-3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [F]
  have hnotconj :
      ¬ ∃ P Q : Matrix (Fin 2) (Fin 2) ℝ,
        P * Q = 1 ∧ Q * P = 1 ∧ Q * F * P = J := by
    rintro ⟨P, Q, hPQ, hQP, hconj⟩
    have hscalar : J = (-3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      calc
        J = Q * F * P := hconj.symm
        _ = Q * ((-3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * P := by rw [hFscalar]
        _ = (-3 : ℝ) • (Q * (1 : Matrix (Fin 2) (Fin 2) ℝ) * P) := by
          simp [mul_assoc]
        _ = (-3 : ℝ) • (Q * P) := by simp
        _ = (-3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by rw [hQP]
    have hentry := congrFun (congrFun hscalar 0) 1
    norm_num [J] at hentry
  exact ⟨hcharF, hcharJ, htrace_pos, hFzero, hJnonzero, hJnil, hnotconj⟩

end MathlibPlus.LinearAlgebra
