import MathlibPlus.Basic

open scoped BigOperators

namespace MathlibPlus.Algebra.Claim4842

variable {R : Type*} [CommRing R]

/-- The complete-homogeneous sequence of a finite alphabet, represented as a list.

The recursive presentation is the usual decomposition by the multiplicity of the
first knot.  It is used here only through its first `N + 1` entries. -/
def completeHomogeneousList : List R → ℕ → R
  | [], 0 => 1
  | [], _ + 1 => 0
  | _ :: _, 0 => 1
  | z :: Z, n + 1 =>
      ∑ k ∈ Finset.range (n + 2), z ^ k * completeHomogeneousList Z (n + 1 - k)

private lemma completeHomogeneousList_zero (Z : List R) :
    completeHomogeneousList Z 0 = 1 := by
  induction Z with
  | nil => rfl
  | cons z Z ih => rfl

private lemma completeHomogeneousList_cons (z : R) (Z : List R) (n : ℕ) :
    completeHomogeneousList (z :: Z) n =
      ∑ k ∈ Finset.range (n + 1),
        z ^ k * completeHomogeneousList Z (n - k) := by
  cases n with
  | zero => simp [completeHomogeneousList_zero]
  | succ n => rfl

private lemma movingKnot_sum (N : ℕ) (i : Fin (N + 1)) (z : R)
    (h : Fin (N + 1) → R) :
    (∑ j : Fin (N + 1),
      if j.val ≤ i.val then
        z ^ (i.val - j.val) * h ⟨j.val, by omega⟩
      else 0) =
      ∑ k ∈ Finset.range (i.val + 1),
        z ^ k * h ⟨i.val - k, by omega⟩ := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun j _hj => i.val - j.val)
  · intro j hj
    simp only [Finset.mem_range]
    omega
  · intro j1 hj1 j2 hj2 heq
    have hj1_le : j1.val ≤ i.val := (Finset.mem_filter.mp hj1).2
    have hj2_le : j2.val ≤ i.val := (Finset.mem_filter.mp hj2).2
    apply Fin.ext
    omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    refine ⟨⟨i.val - k, by omega⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · have hk_le : k ≤ i.val := Nat.le_of_lt_succ hk
      have hnat : i.val - (i.val - k) = k := Nat.sub_sub_self hk_le
      simpa using hnat
  · intro j hj
    have hj_le : j.val ≤ i.val := (Finset.mem_filter.mp hj).2
    have heqfin :
        (⟨j.val, by omega⟩ : Fin (N + 1)) =
          ⟨i.val - (i.val - j.val), by omega⟩ := by
      apply Fin.ext
      have hnat : i.val - (i.val - j.val) = j.val :=
        Nat.sub_sub_self hj_le
      simpa using hnat.symm
    rw [heqfin]

/-- Claim 4842: adjoining a knot `z` acts on the first `N + 1` complete-
 homogeneous coordinates by the lower-triangular Toeplitz matrix with
 `(a,b)` entry `z^(a-b)` for `b ≤ a` and zero otherwise. -/
theorem movingKnotJetTransfer (N : ℕ) (z : R) (Z : List R) :
    let old : Fin (N + 1) → R :=
      fun i => completeHomogeneousList Z i.val
    let new : Fin (N + 1) → R :=
      fun i => completeHomogeneousList (z :: Z) i.val
    let T : Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
      fun i j => if j.val ≤ i.val then z ^ (i.val - j.val) else 0
    new = T.mulVec old := by
  dsimp
  funext i
  rw [completeHomogeneousList_cons]
  change
    (∑ k ∈ Finset.range (i.val + 1),
        z ^ k * completeHomogeneousList Z (i.val - k)) =
      ∑ j : Fin (N + 1),
        (if j.val ≤ i.val then z ^ (i.val - j.val) else 0) *
          completeHomogeneousList Z j.val
  simp_rw [ite_mul]
  simpa using
    (movingKnot_sum N i z (fun j => completeHomogeneousList Z j.val)).symm

end MathlibPlus.Algebra.Claim4842
