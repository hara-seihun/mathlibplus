import Mathlib

namespace MathlibPlus
namespace Combinatorics

/-- The displayed one-mode degree is maximized uniquely at `b=1` among
positive mode indices. -/
theorem central_degree_one_mode_maximum_claim8020
    (m b : ℤ) (hb : 1 ≤ b) :
    m ^ 2 - (b - 1) ^ 2 ≤ m ^ 2 ∧
      (m ^ 2 - (b - 1) ^ 2 = m ^ 2 ↔ b = 1) := by
  constructor
  · nlinarith [sq_nonneg (b - 1)]
  · constructor
    · intro h
      have : (b - 1) ^ 2 = 0 := by nlinarith
      nlinarith
    · intro h
      subst b
      norm_num

end Combinatorics
end MathlibPlus
