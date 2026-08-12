import Mathlib

namespace MathlibPlus.LinearAlgebra

open Polynomial

/-- Claim 10500, formalized over every field of characteristic three (and hence over
`𝔽₉`): the scalar and nontrivial Jordan matrices have identical traces of all
natural powers, but different minimal polynomials. -/
theorem equalPowerTracesDifferentMinpoly_claim10500
    {K : Type*} [Field K] [CharP K 3] :
    let S : Matrix (Fin 2) (Fin 2) K := !![(-3 : K), 0; 0, -3]
    let J : Matrix (Fin 2) (Fin 2) K := !![(-3 : K), 1; 0, -3]
    (∀ k : ℕ,
      Matrix.trace (S ^ k) = 2 * (-3 : K) ^ k ∧
        Matrix.trace (J ^ k) = 2 * (-3 : K) ^ k) ∧
      minpoly K S ≠ minpoly K J := by
  dsimp
  let S : Matrix (Fin 2) (Fin 2) K := !![(-3 : K), 0; 0, -3]
  let J : Matrix (Fin 2) (Fin 2) K := !![(-3 : K), 1; 0, -3]
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  have hthree : (-3 : K) = 0 := by
    calc
      (-3 : K) = -(3 : K) := by norm_num
      _ = -0 := by rw [h3]
      _ = 0 := by simp
  have hS : S = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [S, hthree]
  have hJ : J ≠ 0 := by
    intro h
    have h01 := congr_fun (congr_fun h 0) 1
    simp [J] at h01
  have htraceS : ∀ k : ℕ, Matrix.trace (S ^ k) = 2 * (-3 : K) ^ k := by
    intro k
    rw [hS]
    cases k with
    | zero => simp [Matrix.trace, Fin.sum_univ_two]
    | succ k => simp [hthree]
  have hJ0 : J = !![0, 1; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J, hthree]
  have hJ2 : J ^ 2 = 0 := by
    rw [hJ0]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  have hJpow (k : ℕ) : J ^ (k + 2) = 0 := by
    induction k with
    | zero => simpa using hJ2
    | succ k ih =>
      rw [show k + 1 + 2 = (k + 2) + 1 by omega, pow_succ, ih, zero_mul]
  have htraceJ : ∀ k : ℕ, Matrix.trace (J ^ k) = 2 * (-3 : K) ^ k := by
    intro k
    cases k with
    | zero => simp [Matrix.trace, Fin.sum_univ_two]
    | succ k =>
      cases k with
      | zero => simp [J, hthree, Matrix.trace, Fin.sum_univ_two]
      | succ k =>
        have hp : J ^ Nat.succ (Nat.succ k) = 0 := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hJpow k
        rw [hp]
        simp [hthree]
  have hminS : minpoly K S = Polynomial.X := by
    rw [hS]
    exact minpoly.zero K _
  have hmin_ne : minpoly K S ≠ minpoly K J := by
    intro heq
    have hminJ : minpoly K J = Polynomial.X := (hminS.symm.trans heq).symm
    have hzero := minpoly.aeval K J
    rw [hminJ] at hzero
    have hJzero : J = 0 := by simpa using hzero
    exact hJ hJzero
  exact ⟨fun k => ⟨htraceS k, htraceJ k⟩, hmin_ne⟩

end MathlibPlus.LinearAlgebra
