import Mathlib

namespace MathlibPlus
namespace Combinatorics

/-- The odd tail of the displayed lower-full capacity formula simplifies to
`(k - 9) / 2` once `k ≥ 17`. -/
theorem lower_full_capacity_odd_tail_claim23866
    (C : ℕ → ℕ)
    (hC : ∀ k : ℕ, 11 ≤ k → Odd k →
      C k = 3 + max 0 ((k - 15) / 2)) :
    ∀ k : ℕ, 17 ≤ k → Odd k → C k = (k - 9) / 2 := by
  intro k hk hodd
  rw [hC k (by omega) hodd]
  simp only [Nat.zero_max]
  omega

end Combinatorics
end MathlibPlus
