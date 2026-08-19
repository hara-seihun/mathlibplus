import Mathlib.Tactic

namespace MathlibPlus.Combinatorics.IntervalSplitSupport

open Set

/-- At radius three, the split profile of every interval of length at least six
has exactly the five saturated endpoint types. -/
theorem interval_split_support_saturation {L : ℕ} (hL : 6 ≤ L) :
    {p : ℕ × ℕ | ∃ i : ℕ, 1 ≤ i ∧ i < L ∧
      p = (min i 3, min (L - i) 3)} =
      ({(1, 3), (2, 3), (3, 3), (3, 2), (3, 1)} : Set (ℕ × ℕ)) := by
  ext p
  constructor
  · rintro ⟨i, hi, hiL, rfl⟩
    by_cases hil : i ≤ 3
    · have hil' : i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hil' with rfl | rfl | rfl
      · have htail : 3 ≤ L - 1 := by omega
        rw [min_eq_left (by omega), min_eq_right htail]
        simp
      · have htail : 3 ≤ L - 2 := by omega
        rw [min_eq_left (by omega), min_eq_right htail]
        simp
      · have htail : 3 ≤ L - 3 := by omega
        rw [min_eq_left (by omega), min_eq_right htail]
        simp
    · have hil' : 3 ≤ i := by omega
      have hLi : 1 ≤ L - i := by omega
      by_cases hLi3 : L - i ≤ 3
      · have hLi' : L - i = 1 ∨ L - i = 2 ∨ L - i = 3 := by omega
        have hfirst : min i 3 = 3 := min_eq_right hil'
        have hsecond : min (L - i) 3 = L - i := min_eq_left hLi3
        rw [hfirst, hsecond]
        rcases hLi' with hLi' | hLi' | hLi' <;> simp [hLi']
      · have hLi' : 3 ≤ L - i := by omega
        rw [min_eq_right hil', min_eq_right hLi']
        simp
  · intro hp
    simp only [mem_insert_iff, mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · refine ⟨1, by omega, by omega, ?_⟩
      have htail : 3 ≤ L - 1 := by omega
      rw [min_eq_left (by omega), min_eq_right htail]
    · refine ⟨2, by omega, by omega, ?_⟩
      have htail : 3 ≤ L - 2 := by omega
      rw [min_eq_left (by omega), min_eq_right htail]
    · refine ⟨3, by omega, by omega, ?_⟩
      have htail : 3 ≤ L - 3 := by omega
      rw [min_eq_left (by omega), min_eq_right htail]
    · refine ⟨L - 2, by omega, by omega, ?_⟩
      have hfirst : min (L - 2) 3 = 3 := min_eq_right (by omega)
      have hsub : L - (L - 2) = 2 := by omega
      rw [hfirst, hsub]
      rfl
    · refine ⟨L - 1, by omega, by omega, ?_⟩
      have hfirst : min (L - 1) 3 = 3 := min_eq_right (by omega)
      have hsub : L - (L - 1) = 1 := by omega
      rw [hfirst, hsub]
      rfl

end MathlibPlus.Combinatorics.IntervalSplitSupport
