import Mathlib

namespace MathlibPlus.Algebra.Claim57725

/-- Claim 57725: a finite nonzero coefficient packet of total mass zero has
matching positive and negative masses, and that common mass is at least one. -/
theorem positive_negative_mass_claim57725
    {α : Type*} [Fintype α] (c : α → ℤ)
    (hsum : ∑ a, c a = 0) (hnonzero : ∃ a, c a ≠ 0) :
    let Mpos : ℤ := ∑ a, max (c a) 0
    let Mneg : ℤ := ∑ a, max (-c a) 0
    Mpos = Mneg ∧ 1 ≤ Mpos := by
  have hsplit : ∀ n : ℤ, max n 0 - max (-n) 0 = n := by
    intro n
    by_cases hn : 0 ≤ n
    · rw [Int.max_eq_left hn, Int.max_eq_right (neg_nonpos.mpr hn)]
      simp
    · have hn' : n ≤ 0 := le_of_not_ge hn
      rw [Int.max_eq_right hn', Int.max_eq_left (neg_nonneg.mpr hn')]
      omega
  have hmass : (∑ a, max (c a) 0) = ∑ a, max (-c a) 0 := by
    have hpoint : ∀ a : α, max (c a) 0 = c a + max (-c a) 0 := by
      intro a
      have h := hsplit (c a)
      omega
    calc
      (∑ a, max (c a) 0) = ∑ a, (c a + max (-c a) 0) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hpoint a
      _ = (∑ a, c a) + ∑ a, max (-c a) 0 := by
        rw [Finset.sum_add_distrib]
      _ = ∑ a, max (-c a) 0 := by simp [hsum]
  obtain ⟨a₀, ha₀⟩ := hnonzero
  have hpos_nonneg : ∀ a : α, 0 ≤ max (c a) 0 := by
    intro a
    exact le_max_right _ _
  have hneg_nonneg : ∀ a : α, 0 ≤ max (-c a) 0 := by
    intro a
    exact le_max_right _ _
  have hpos_sum : max (c a₀) 0 ≤ ∑ a, max (c a) 0 := by
    simpa using
      (Finset.single_le_sum (s := (Finset.univ : Finset α))
        (f := fun a => max (c a) 0)
        (fun a ha => hpos_nonneg a) (Finset.mem_univ a₀))
  have hneg_sum : max (-c a₀) 0 ≤ ∑ a, max (-c a) 0 := by
    simpa using
      (Finset.single_le_sum (s := (Finset.univ : Finset α))
        (f := fun a => max (-c a) 0)
        (fun a ha => hneg_nonneg a) (Finset.mem_univ a₀))
  have hmass_one : 1 ≤ (∑ a, max (c a) 0) := by
    by_cases hcp : 0 < c a₀
    · have hone : 1 ≤ max (c a₀) 0 := by omega
      exact le_trans hone hpos_sum
    · have hcn : c a₀ < 0 := by omega
      have hone : 1 ≤ max (-c a₀) 0 := by omega
      exact le_trans hone (by simpa [hmass] using hneg_sum)
  dsimp
  exact ⟨hmass, hmass_one⟩

end MathlibPlus.Algebra.Claim57725
