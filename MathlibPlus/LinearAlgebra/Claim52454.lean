import Mathlib

open scoped BigOperators

namespace MathlibPlus.LinearAlgebra

def allOnesMatrix_claim52454 (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun _ _ => 1

def completeAdjacencyMatrix_claim52454 (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  allOnesMatrix_claim52454 n - 1

private theorem completeAdjacency_diag_claim52454
    (n : ℕ) (i : Fin n) :
    (completeAdjacencyMatrix_claim52454 n *
        completeAdjacencyMatrix_claim52454 n) i i = (n : ℤ) - 1 := by
  change (∑ x : Fin n, ((1 : ℤ) - (if i = x then 1 else 0)) *
      (1 - (if x = i then 1 else 0))) = (n : ℤ) - 1
  have hterm (x : Fin n) :
      ((1 : ℤ) - (if i = x then 1 else 0)) *
        (1 - (if x = i then 1 else 0)) =
          1 - (if i = x then 1 else 0) := by
    by_cases hix : i = x
    · simp [hix]
    · have hxi : x ≠ i := Ne.symm hix
      simp [hix, hxi]
  calc
    (∑ x : Fin n, ((1 : ℤ) - (if i = x then 1 else 0)) *
        (1 - (if x = i then 1 else 0))) =
        ∑ x : Fin n, ((1 : ℤ) - (if i = x then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hterm x
    _ = (n : ℤ) - 1 := by
      rw [Finset.sum_sub_distrib]
      simp [Finset.sum_const]

private theorem completeAdjacency_offdiag_claim52454
    (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    (completeAdjacencyMatrix_claim52454 n *
        completeAdjacencyMatrix_claim52454 n) i j = (n : ℤ) - 2 := by
  change (∑ x : Fin n, ((1 : ℤ) - (if i = x then 1 else 0)) *
      (1 - (if x = j then 1 else 0))) = (n : ℤ) - 2
  have hterm (x : Fin n) :
      ((1 : ℤ) - (if i = x then 1 else 0)) *
        (1 - (if x = j then 1 else 0)) =
          1 - (if i = x then 1 else 0) - (if x = j then 1 else 0) := by
    by_cases hix : i = x
    · by_cases hxj : x = j
      · exfalso
        exact h (hix.trans hxj)
      · simp [hix, hxj]
    · by_cases hxj : x = j
      · have hij : i ≠ j := by
          intro hij
          exact hix (hij.trans hxj.symm)
        simp [hix, hxj, hij]
      · simp [hix, hxj]
  calc
    (∑ x : Fin n, ((1 : ℤ) - (if i = x then 1 else 0)) *
        (1 - (if x = j then 1 else 0))) =
        ∑ x : Fin n, (1 - (if i = x then 1 else 0) -
          (if x = j then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hterm x
    _ = (n : ℤ) - 2 := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      simp [Finset.sum_const, Fintype.sum_ite_eq, Fintype.sum_ite_eq']
      ring

/-- The ambient vector-space carrier in claim 52454 has the displayed
cardinality. -/
theorem claim52454_vertex_card :
    (5 : ℕ) ^ 6 = 15625 := by
  norm_num

/-- The exact adjacency-square identity for the complete graph on 15625
vertices, retaining the matrix form `A = J - I` of claim 52454. -/
theorem claim52454_complete_adjacency_square :
    completeAdjacencyMatrix_claim52454 15625 *
        completeAdjacencyMatrix_claim52454 15625 =
      (15625 - 2 : ℤ) • allOnesMatrix_claim52454 15625 + 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    rw [completeAdjacency_diag_claim52454]
    simp only [Matrix.add_apply, Matrix.smul_apply,
      allOnesMatrix_claim52454, Matrix.one_apply]
    norm_num
  · rw [completeAdjacency_offdiag_claim52454 _ _ _ h]
    simp only [Matrix.add_apply, Matrix.smul_apply,
      allOnesMatrix_claim52454, Matrix.one_apply, h]
    norm_num

end MathlibPlus.LinearAlgebra
