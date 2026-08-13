import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics

/-- Pairwise distinct singleton intersections preclude a three-sunflower.
The hypotheses are the intersection and distinct-edge facts in claim 46184;
``A i ∩ A j = A i ∩ A k = A j ∩ A k`` is the three-set sunflower
condition (the common core is not required to be named). -/
theorem pairwiseDistinctSingletonIntersections_noThreeSunflower_claim46184
    {ι α : Type*} [DecidableEq α]
    (A : ι → Finset α) (e : ι → ι → α)
    (h_inter : ∀ ⦃i j : ι⦄, i ≠ j → A i ∩ A j = {e i j})
    (h_distinct : ∀ ⦃i j k : ι⦄,
      i ≠ j → i ≠ k → j ≠ k →
        e i j ≠ e i k ∧ e i j ≠ e j k ∧ e i k ≠ e j k) :
    ¬ ∃ i j k : ι,
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      A i ∩ A j = A i ∩ A k ∧
      A i ∩ A j = A j ∩ A k := by
  rintro ⟨i, j, k, hij, hik, hjk, h_ij_ik, h_ij_jk⟩
  have h_singletons : ({e i j} : Finset α) = {e i k} := by
    rw [← h_inter hij, ← h_inter hik]
    exact h_ij_ik
  have h_equal : e i j = e i k := by
    simpa using h_singletons
  exact (h_distinct hij hik hjk).1 h_equal

end MathlibPlus.Combinatorics
