import Mathlib

namespace MathlibPlus.NumberTheory

/-- The complete nonnegative solution table for `s + p * e = 12` when `p` is
prime and at least five (admitted claim 31044). -/
theorem completePrimeSolutionTable_31044 :
    ∀ {p s e : ℕ}, Nat.Prime p → 5 ≤ p →
      (s + p * e = 12 ↔
        (p = 5 ∧ ((s = 12 ∧ e = 0) ∨ (s = 7 ∧ e = 1) ∨
          (s = 2 ∧ e = 2))) ∨
        ((p = 7 ∨ p = 11) ∧
          ((s = 12 ∧ e = 0) ∨ (s + p = 12 ∧ e = 1))) ∨
        (13 ≤ p ∧ s = 12 ∧ e = 0)) := by
  intro p s e hp hp5
  constructor
  · intro heq
    have he_le : e ≤ 2 := by
      by_contra h
      have he3 : 3 ≤ e := by omega
      nlinarith
    interval_cases e
    · have hs : s = 12 := by omega
      by_cases hp13 : 13 ≤ p
      · exact Or.inr (Or.inr ⟨hp13, hs, rfl⟩)
      · have hp_lt13 : p < 13 := by omega
        interval_cases p <;> norm_num at hp
        all_goals omega
    · have hp_le12 : p ≤ 12 := by omega
      have hs : s + p = 12 := by omega
      interval_cases p <;> norm_num at hp
      all_goals omega
    · have hp_le6 : p ≤ 6 := by omega
      interval_cases p <;> norm_num at hp
      all_goals omega
  · intro h
    rcases h with h | h | h
    · rcases h with ⟨rfl, hs⟩
      rcases hs with h0 | h1 | h2
      · rcases h0 with ⟨rfl, rfl⟩
        norm_num
      · rcases h1 with ⟨rfl, rfl⟩
        norm_num
      · rcases h2 with ⟨rfl, rfl⟩
        norm_num
    · rcases h with ⟨hp7or11, hs⟩
      rcases hp7or11 with rfl | rfl
      · rcases hs with ⟨⟨rfl, rfl⟩ | ⟨hs, rfl⟩⟩ <;> omega
      · rcases hs with ⟨⟨rfl, rfl⟩ | ⟨hs, rfl⟩⟩ <;> omega
    · rcases h with ⟨hp13, rfl, rfl⟩
      norm_num

end MathlibPlus.NumberTheory
