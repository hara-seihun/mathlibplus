import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- A private row for each column forces the column family to be linearly
independent.  This is the algebraic core of the private-signature argument. -/
theorem privateSignature_columns_linearIndependent_claim14346
    {K I J : Type*} [Field K] [Fintype I]
    (M : J → I → K)
    (hprivate : ∀ i : I, ∃ j : J,
      M j i ≠ 0 ∧ ∀ k : I, k ≠ i → M j k = 0) :
    LinearIndependent K (fun i : I => fun j : J => M j i) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  obtain ⟨j, hji, hzero⟩ := hprivate i
  have hrow := congrFun hg j
  have hsum : (∑ k : I, g k * M j k) = 0 := by
    simpa only [Finset.sum_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul] using hrow
  have hcollapse : (∑ k : I, g k * M j k) = g i * M j i := by
    apply Finset.sum_eq_single i
    · intro k hk hki
      rw [hzero k hki, mul_zero]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  have hprod : g i * M j i = 0 := by
    rw [← hcollapse]
    exact hsum
  exact (mul_eq_zero.mp hprod).resolve_right hji

/-- The same private-signature hypothesis gives full column rank. -/
theorem privateSignature_full_column_rank_claim14346
    {K I J : Type*} [Field K] [Fintype I] [Fintype J]
    (M : Matrix J I K)
    (hprivate : ∀ i : I, ∃ j : J,
      M j i ≠ 0 ∧ ∀ k : I, k ≠ i → M j k = 0) :
    M.rank = Fintype.card I := by
  have hli : LinearIndependent K (fun i : I => fun j : J => M j i) :=
    privateSignature_columns_linearIndependent_claim14346 M hprivate
  have hrows : LinearIndependent K (M.transpose.row) := by
    change LinearIndependent K (fun i : I => fun j : J => M j i)
    exact hli
  have hrank : M.transpose.rank = Fintype.card I :=
    LinearIndependent.rank_matrix hrows
  simpa only [Matrix.rank_transpose] using hrank

end MathlibPlus.LinearAlgebra
