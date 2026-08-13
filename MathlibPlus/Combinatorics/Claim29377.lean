import Mathlib

namespace MathlibPlus.Combinatorics

private lemma filter_eq_one_replicate (C : Multiset ℕ) :
    C.filter (fun a => ¬ a ≠ 1) = Multiset.replicate (C.count 1) 1 := by
  apply Multiset.ext.mpr
  intro a
  by_cases ha : a = 1
  · subst a
    simp
  · have h1a : (1 : ℕ) ≠ a := Ne.symm ha
    simp [ha, h1a, Multiset.count_replicate]

private lemma sum_eq_filtered_ne_one_add_count_one (C : Multiset ℕ) :
    C.sum = (C.filter (fun a => a ≠ 1)).sum + C.count 1 := by
  have h := Multiset.sum_filter_add_sum_filter_not (fun a : ℕ => a ≠ 1) (s := C)
  rw [filter_eq_one_replicate, Multiset.sum_replicate] at h
  simpa using h.symm

/-- The multiplicity of the unit leg is the total length minus the
sum of the nonunit legs. -/
theorem count_one_eq_sum_sub_nonunit_sum_claim29377
    (C : Multiset ℕ) (hC : ∀ a, a ∈ C → 0 < a) :
    C.count 1 = C.sum - (C.filter (fun a => a ≠ 1)).sum := by
  have hCsum := sum_eq_filtered_ne_one_add_count_one C
  omega

/-- Claim 29377: for positive leg multisets, the nonunit lengths and total
length determine the full multiset, including the multiplicity of length one. -/
theorem nonunit_multiset_eq_of_sum_eq_claim29377
    (C D : Multiset ℕ)
    (hC : ∀ a, a ∈ C → 0 < a)
    (hD : ∀ a, a ∈ D → 0 < a)
    (hfilter : C.filter (fun a => a ≠ 1) = D.filter (fun a => a ≠ 1))
    (hsum : C.sum = D.sum) :
    C = D := by
  have hCsum := sum_eq_filtered_ne_one_add_count_one C
  have hDsum := sum_eq_filtered_ne_one_add_count_one D
  have hone : C.count 1 = D.count 1 := by
    rw [hsum, hfilter] at hCsum
    omega
  apply Multiset.ext.mpr
  intro a
  by_cases ha : a = 1
  · simpa [ha] using hone
  · have hcount := congrArg (Multiset.count a) hfilter
    simpa [Multiset.count_filter, ha] using hcount

end MathlibPlus.Combinatorics
