import Mathlib

namespace MathlibPlus.Combinatorics.Claim32810

/-- The unrestricted finite bound follows from the bounded-matching bound by
binomial expansion. The counting functions are left abstract, while the
fixed parameter `k`, the subclass inequality, and the trace inequality remain
explicit. -/
theorem constantBaseTransfer_claim32810
    (G M : ℕ → ℕ → ℕ) (k C : ℕ)
    (hsub : ∀ n, G k n ≤ M k n)
    (hbound : ∀ r, G k r ≤ C ^ r)
    (htrace : ∀ n, M k n ≤
      1 + ∑ r ∈ Finset.range n, n.choose (r + 1) * G k (r + 1)) :
    (∀ n, G k n ≤ M k n) ∧ (∀ n, M k n ≤ (1 + C) ^ n) := by
  refine ⟨hsub, ?_⟩
  intro n
  calc
    M k n ≤ 1 + ∑ r ∈ Finset.range n, n.choose (r + 1) * G k (r + 1) := htrace n
    _ ≤ 1 + ∑ r ∈ Finset.range n, n.choose (r + 1) * C ^ (r + 1) := by
      gcongr with r hr
      exact hbound (r + 1)
    _ = (1 + C) ^ n := by
      have hbin := add_pow C 1 n
      rw [add_comm C 1] at hbin
      rw [Finset.sum_range_succ'] at hbin
      calc
        1 + ∑ r ∈ Finset.range n, n.choose (r + 1) * C ^ (r + 1) =
            (∑ r ∈ Finset.range n, C ^ (r + 1) * n.choose (r + 1)) + 1 := by
              ac_rfl
        _ = (1 + C) ^ n := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using hbin.symm

end MathlibPlus.Combinatorics.Claim32810
