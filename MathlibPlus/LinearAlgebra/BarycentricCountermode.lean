import Mathlib

open scoped BigOperators
open Polynomial

namespace MathlibPlus.LinearAlgebra.BarycentricCountermode

private lemma prod_X_sub_C_natDegree {F : Type*} [Field F] {n : ℕ}
    (x : Fin (n + 1) → F) (i : Fin (n + 1)) :
    (∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        (X - C (x j))).natDegree = n := by
  rw [Polynomial.natDegree_prod' (s := (Finset.univ : Finset (Fin (n + 1))).erase i)
    (f := fun j : Fin (n + 1) => X - C (x j))]
  · simp [Finset.card_erase_of_mem (Finset.mem_univ i)]
  · simp

private lemma prod_X_sub_C_coeff_top {F : Type*} [Field F] {n : ℕ}
    (x : Fin (n + 1) → F) (i : Fin (n + 1)) :
    (∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        (X - C (x j))).coeff n = 1 := by
  have hmonic := Polynomial.monic_prod_X_sub_C x
    ((Finset.univ : Finset (Fin (n + 1))).erase i)
  have hnd := prod_X_sub_C_natDegree x i
  simpa [hnd] using hmonic.coeff_natDegree

/--
Claim 18770's explicit minimal barycentric countermode.  For distinct nodes
`x₀, …, xₙ`, the reciprocal Vandermonde weights annihilate the moments below
`n` and normalize the `n`th moment to one.
-/
theorem barycentricCountermode {F : Type*} [Field F] {n : ℕ}
    (x : Fin (n + 1) → F) (hx : Function.Injective x) :
    (∀ k : ℕ, k < n →
      ∑ i : Fin (n + 1),
        (∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          (x i - x j))⁻¹ * x i ^ k = 0) ∧
      (∑ i : Fin (n + 1),
        (∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          (x i - x j))⁻¹ * x i ^ n = 1) := by
  have hinj : Set.InjOn x (↑(Finset.univ : Finset (Fin (n + 1))) : Set (Fin (n + 1))) := by
    simpa [Finset.coe_univ] using hx
  have hbase (k : ℕ) (hk : k < n + 1) :
      X ^ k = Lagrange.interpolate (Finset.univ : Finset (Fin (n + 1))) x
        (fun i => x i ^ k) := by
    have heq := Lagrange.eq_interpolate (s := (Finset.univ : Finset (Fin (n + 1))))
      (v := x) (f := X ^ k) hinj (by
        rw [Polynomial.degree_X_pow, Finset.card_univ, Fintype.card_fin]
        exact_mod_cast hk)
    simpa using heq
  have hcoeff (k : ℕ) (hk : k < n + 1) :
      (X ^ k).coeff n =
        ∑ i : Fin (n + 1),
          (x i ^ k / (∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
            (x i - x j))) := by
    have h := congrArg (fun p : F[X] => p.coeff n) (hbase k hk)
    rw [Lagrange.interpolate_eq_sum] at h
    rw [Polynomial.finsetSum_coeff] at h
    simp_rw [Polynomial.coeff_C_mul, prod_X_sub_C_coeff_top x] at h
    simpa only [mul_one] using h
  constructor
  · intro k hk
    have h := hcoeff k (Nat.lt_trans hk (Nat.lt_succ_self n))
    have hkne : n ≠ k := Nat.ne_of_gt hk
    have h' := h.symm
    simpa [Polynomial.coeff_X_pow, hkne, div_eq_mul_inv, mul_comm] using h'
  · have h := hcoeff n (Nat.lt_succ_self n)
    have h' := h.symm
    simpa [Polynomial.coeff_X_pow, div_eq_mul_inv, mul_comm] using h'

end MathlibPlus.LinearAlgebra.BarycentricCountermode
