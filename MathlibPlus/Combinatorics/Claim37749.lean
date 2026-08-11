import Mathlib

namespace MathlibPlus.Combinatorics.Claim37749

/-- In a packing of finite blocks of total order `r`, there cannot be two
selected blocks of order `J` when `J ≤ r < 2J`.  This is the formal core of
the one-marker-band lemma in claim 37749; the forest/connectedness hypotheses
are not used by the counting argument. -/
theorem atMostOneSelectedJBlock
    {ι : Type*} (S : Finset ι) (size : ι → ℕ)
    (J r : ℕ) (_hJ : 2 ≤ J) (_hlo : J ≤ r) (hhi : r < 2 * J)
    (htotal : ∑ x ∈ S, size x = r) :
    (S.filter (fun x => size x = J)).card ≤ 1 := by
  by_contra hnot
  have hnot' : ¬ (∀ a ∈ S.filter (fun x => size x = J),
      ∀ b ∈ S.filter (fun x => size x = J), a = b) := by
    intro hall
    exact hnot (Finset.card_le_one.mpr hall)
  push_neg at hnot'
  classical
  obtain ⟨x, hx, y, hy, hxy⟩ := hnot'
  have hxJ : size x = J := (Finset.mem_filter.mp hx).2
  have hyJ : size y = J := (Finset.mem_filter.mp hy).2
  have hsubset : ({x, y} : Finset ι) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact (Finset.mem_filter.mp hx).1
    · exact (Finset.mem_filter.mp hy).1
  have hsum : size x + size y ≤ (∑ z ∈ S, size z) := by
    calc
      size x + size y = (∑ z ∈ ({x, y} : Finset ι), size z) := by
        simp [hxy]
      _ ≤ (∑ z ∈ S, size z) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
          intro z hz hzs
          exact Nat.zero_le _)
  rw [hxJ, hyJ, htotal] at hsum
  omega

end MathlibPlus.Combinatorics.Claim37749
