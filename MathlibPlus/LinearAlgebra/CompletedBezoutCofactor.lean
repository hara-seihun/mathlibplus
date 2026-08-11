import Mathlib

open scoped BigOperators

namespace MathlibPlus.LinearAlgebra.CompletedBezout

open Matrix

private lemma det_update_last_diagonal {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (d : ℝ) :
    det (M.updateRow (Fin.last n)
        ((fun j => M (Fin.last n) j) + d • Pi.single (Fin.last n) 1)) =
      det M + d * det (M.submatrix Fin.castSucc Fin.castSucc) := by
  rw [det_updateRow_add]
  have hself : M.updateRow (Fin.last n) (fun j => M (Fin.last n) j) = M :=
    updateRow_eq_self M (Fin.last n)
  rw [hself, det_updateRow_smul]
  rw [← adjugate_apply]
  rw [adjugate_fin_succ_eq_det_submatrix]
  simp

/-- Changing only the highest coefficient in a completed Bezout matrix changes its
 determinant by the bottom-right cofactor times the exact coefficient of that entry. -/
theorem det_change_highestCoeff (n : ℕ) (_hn : 1 ≤ n) (h : ℕ → ℝ) (x : ℝ) :
    let h' := Function.update h (2 * n + 1) (h (2 * n + 1) + x)
    let C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j =>
      ∑ a ∈ Finset.range (min i.1 j.1 + 1),
        ((i.1 + j.1 + 1 - 2 * a : ℕ) : ℝ) * h a * h (i.1 + j.1 + 1 - a)
    let C' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j =>
      ∑ a ∈ Finset.range (min i.1 j.1 + 1),
        ((i.1 + j.1 + 1 - 2 * a : ℕ) : ℝ) * h' a * h' (i.1 + j.1 + 1 - a)
    let Cprev : Matrix (Fin n) (Fin n) ℝ := fun i j =>
      ∑ a ∈ Finset.range (min i.1 j.1 + 1),
        ((i.1 + j.1 + 1 - 2 * a : ℕ) : ℝ) * h a * h (i.1 + j.1 + 1 - a)
    det C' = det C + x * ((2 * n + 1 : ℕ) : ℝ) * h 0 * det Cprev := by
  dsimp only
  let C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j =>
    ∑ a ∈ Finset.range (min i.1 j.1 + 1),
      ((i.1 + j.1 + 1 - 2 * a : ℕ) : ℝ) * h a * h (i.1 + j.1 + 1 - a)
  let C' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j =>
    ∑ a ∈ Finset.range (min i.1 j.1 + 1),
      ((i.1 + j.1 + 1 - 2 * a : ℕ) : ℝ) *
        (Function.update h (2 * n + 1) (h (2 * n + 1) + x)) a *
        (Function.update h (2 * n + 1) (h (2 * n + 1) + x)) (i.1 + j.1 + 1 - a)
  let Cprev : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    ∑ a ∈ Finset.range (min i.1 j.1 + 1),
      ((i.1 + j.1 + 1 - 2 * a : ℕ) : ℝ) * h a * h (i.1 + j.1 + 1 - a)
  change det C' = det C + x * ((2 * n + 1 : ℕ) : ℝ) * h 0 * det Cprev
  have hCprev : C.submatrix Fin.castSucc Fin.castSucc = Cprev := by
    rfl
  have hmatrix : C' = C.updateRow (Fin.last n)
      ((fun j => C (Fin.last n) j) +
        (x * ((2 * n + 1 : ℕ) : ℝ) * h 0) • Pi.single (Fin.last n) 1) := by
    ext i j
    by_cases hi : i = Fin.last n
    · subst i
      rw [Matrix.updateRow_self]
      by_cases hj : j = Fin.last n
      · subst j
        simp only [C', C, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
          mul_one, Fin.val_last, min_self]
        rw [← two_mul n]
        calc
          (∑ a ∈ Finset.range (n + 1),
              ((2 * n + 1 - 2 * a : ℕ) : ℝ) *
                (Function.update h (2 * n + 1) (h (2 * n + 1) + x)) a *
                (Function.update h (2 * n + 1) (h (2 * n + 1) + x)) (2 * n + 1 - a)) =
              ∑ a ∈ Finset.range (n + 1),
                (((2 * n + 1 - 2 * a : ℕ) : ℝ) * h a * h (2 * n + 1 - a) +
                  if a = 0 then x * ((2 * n + 1 : ℕ) : ℝ) * h 0 else 0) := by
                    apply Finset.sum_congr rfl
                    intro a ha
                    have ha_lt : a < n + 1 := Finset.mem_range.mp ha
                    by_cases ha0 : a = 0
                    · subst a
                      simp
                      ring
                    · have ha_ne : a ≠ 2 * n + 1 := by omega
                      have hsub_ne : 2 * n + 1 - a ≠ 2 * n + 1 := by omega
                      simp [ha0, Function.update_of_ne ha_ne,
                        Function.update_of_ne hsub_ne]
          _ = (∑ a ∈ Finset.range (n + 1),
                  ((2 * n + 1 - 2 * a : ℕ) : ℝ) * h a * h (2 * n + 1 - a)) +
                x * ((2 * n + 1 : ℕ) : ℝ) * h 0 := by
                  rw [Finset.sum_add_distrib]
                  simp
      · have hjne : j.1 ≠ n := by
          intro heq
          apply hj
          apply Fin.ext
          simpa using heq
        have hjlt : j.1 < n := by omega
        simp only [C', C, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hj,
          smul_eq_mul, mul_zero, add_zero, Fin.val_last]
        apply Finset.sum_congr rfl
        intro a ha
        have ha_le : a ≤ min n j.1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        have ha_ne : a ≠ 2 * n + 1 := by omega
        have hsub_ne : n + j.1 + 1 - a ≠ 2 * n + 1 := by omega
        simp [Function.update_of_ne ha_ne, Function.update_of_ne hsub_ne]
    · rw [Matrix.updateRow_ne hi]
      have hine : i.1 ≠ n := by
        intro heq
        apply hi
        apply Fin.ext
        simpa using heq
      have hilt : i.1 < n := by
        have hile : i.1 ≤ n := Nat.le_of_lt_succ i.2
        omega
      simp only [C', C]
      apply Finset.sum_congr rfl
      intro a ha
      have ha_le : a ≤ min i.1 j.1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      have ha_ne : a ≠ 2 * n + 1 := by omega
      have hsub_ne : i.1 + j.1 + 1 - a ≠ 2 * n + 1 := by
        have hjle : j.1 ≤ n := Nat.le_of_lt_succ j.2
        omega
      simp [Function.update_of_ne ha_ne, Function.update_of_ne hsub_ne]
  rw [hmatrix, det_update_last_diagonal, hCprev]

end MathlibPlus.LinearAlgebra.CompletedBezout
