import Mathlib

namespace MathlibPlus.Combinatorics

/--
The numerical content of admitted claim 20576.  The bound
`2 ^ (r - n) ≤ 3` forces at most one unit of excess of `r` over `n`, and
there is a boundary case with one unit of excess.

The source does not specify whether the exponent subtraction is intended in
`ℕ` or under an explicit `r ≥ n` hypothesis.  This declaration uses Lean's
literal natural-number subtraction; that convention is left visible for the
fidelity review.
-/
theorem treeFloorDiamond_claim20576 :
    (∀ n r : ℕ, 2 ^ (r - n) ≤ 3 → r ≤ n + 1) ∧
      (∃ n r : ℕ, 2 ^ (r - n) ≤ 3 ∧ ¬ r ≤ n) := by
  constructor
  · intro n r hbound
    by_contra hnot
    have hdiff : 2 ≤ r - n := by omega
    have hpow : 4 ≤ 2 ^ (r - n) := by
      have h := Nat.pow_le_pow_right (show (2 : ℕ) > 0 by omega) hdiff
      norm_num at h ⊢
      exact h
    omega
  · exact ⟨0, 1, by norm_num, by omega⟩

end MathlibPlus.Combinatorics
