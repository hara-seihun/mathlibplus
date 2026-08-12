import Mathlib

namespace MathlibPlus.Algebra

/--
Formalization of admitted claim 37081.  The arithmetic witness is `p = 11`;
the final conjunct records the stronger statement that the proposed
`7p < 7^2` comparison fails for every `p ≥ 11`.
-/
theorem claim37081_uniformC7SelectionFalse :
    (∃ p : ℕ, Nat.Prime p ∧ 11 ≤ p ∧ 7 * p = 77 ∧
      7 ^ 2 = 49 ∧ ¬ (7 * p < 7 ^ 2)) ∧
    (∀ p : ℕ, 11 ≤ p → ¬ (7 * p < 7 ^ 2)) := by
  constructor
  · refine ⟨11, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    norm_num
  · intro p hp hlt
    omega

end MathlibPlus.Algebra
