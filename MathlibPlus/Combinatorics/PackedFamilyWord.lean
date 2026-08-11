import Mathlib

namespace MathlibPlus.Combinatorics.PackedFamilyWord

/-- A family of subsets of an `n`-element finite ground set has `2^n`
possible members.  Through `n = 6`, its indicator therefore fits in 64 bits,
with equality at `n = 6`. -/
theorem packed_family_word_capacity :
    (∀ (α : Type*) [Fintype α],
      Fintype.card (Finset α) = 2 ^ Fintype.card α) ∧
    (∀ n : ℕ, 0 ≤ n → n ≤ 6 → 2 ^ n ≤ 64) ∧
    2 ^ 6 = 64 ∧
    (∀ (α : Type*) [Fintype α], Fintype.card α ≤ 6 →
      Fintype.card (Finset α) ≤ 64) := by
  constructor
  · intro α _
    exact Fintype.card_finset
  constructor
  · intro n _ hn
    interval_cases n <;> norm_num
  constructor
  · norm_num
  · intro α _ hα
    rw [Fintype.card_finset]
    exact (by
      apply (show 2 ^ Fintype.card α ≤ 2 ^ 6 by
        exact Nat.pow_le_pow_right (by omega) hα)
      )

end MathlibPlus.Combinatorics.PackedFamilyWord
