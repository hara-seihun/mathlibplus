import Mathlib

open scoped BigOperators

namespace MathlibPlus.NumberTheory.Claim35041

/-- The finite weighted union bound behind the strict-dual obstruction in claim
35041.  `R` is the target set, `w` is a probability weight on it, and
`sets i b` is the candidate set obtained by choosing option `b` at index `i`.
The supremum is the maximum candidate mass at each index. -/
theorem noCover_of_sumMax_lt_one
    {α ι β : Type*} [Fintype α] [Fintype ι] [Fintype β]
    [Nonempty β] [DecidableEq α]
    (R : Finset α) (w : α → ℝ)
    (h_nonneg : ∀ x, 0 ≤ w x)
    (h_probability : ∑ x ∈ R, w x = 1)
    (sets : ι → β → Finset α)
    (h_phi : ∑ i : ι,
        (Finset.univ : Finset β).sup'
          Finset.univ_nonempty (fun b => ∑ x ∈ sets i b, w x) < 1) :
    ¬ ∃ choice : ι → β,
        ∀ x ∈ R, ∃ i : ι, x ∈ sets i (choice i) := by
  rintro ⟨choice, h_cover⟩
  have hpoint : ∀ x ∈ R,
      w x ≤ ∑ i : ι, if x ∈ sets i (choice i) then w x else 0 := by
    intro x hx
    obtain ⟨i, hi⟩ := h_cover x hx
    have hnon : ∀ j ∈ (Finset.univ : Finset ι),
        0 ≤ (if x ∈ sets j (choice j) then w x else 0) := by
      intro j hj
      split_ifs
      · exact h_nonneg x
      · exact le_rfl
    have hsingle := Finset.single_le_sum hnon (Finset.mem_univ i)
    simpa [hi] using hsingle
  have hsum : 1 ≤
      ∑ x ∈ R, ∑ i : ι, if x ∈ sets i (choice i) then w x else 0 := by
    rw [← h_probability]
    exact Finset.sum_le_sum (fun x hx => hpoint x hx)
  have hsum' : 1 ≤ ∑ i : ι, ∑ x ∈ R,
      if x ∈ sets i (choice i) then w x else 0 := by
    simpa [Finset.sum_comm] using hsum
  have hmass : 1 ≤ ∑ i : ι, ∑ x ∈ sets i (choice i), w x := by
    calc
      1 ≤ ∑ i : ι, ∑ x ∈ R,
          if x ∈ sets i (choice i) then w x else 0 := hsum'
      _ ≤ ∑ i : ι, ∑ x ∈ sets i (choice i), w x := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← Finset.sum_filter]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          exact (Finset.mem_filter.mp hx).2
        · intro x hx hnot
          exact h_nonneg x
  have hupper : (∑ i : ι, ∑ x ∈ sets i (choice i), w x) ≤
      ∑ i : ι, (Finset.univ : Finset β).sup'
        Finset.univ_nonempty (fun b => ∑ x ∈ sets i b, w x) := by
    apply Finset.sum_le_sum
    intro i hi
    exact Finset.le_sup' (s := (Finset.univ : Finset β))
      (fun b => ∑ x ∈ sets i b, w x) (Finset.mem_univ (choice i))
  linarith

end MathlibPlus.NumberTheory.Claim35041
