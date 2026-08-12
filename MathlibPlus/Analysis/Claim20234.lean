import Mathlib

namespace MathlibPlus.Analysis.Claim20234

/-- Claim 20234: the finite and analytic integer cutoffs are adjacent, so no
integer is omitted and the two ranges do not overlap. -/
theorem exactFiniteTailCutoffAdjacency_claim20234 :
    let N : ℕ := 174767473
    let tailStart : ℕ := 174767474
    tailStart = N + 1 ∧
      (∀ n : ℕ, n ≤ N → n < tailStart) ∧
      (∀ n : ℕ, tailStart ≤ n → N < n) := by
  norm_num
  constructor
  · intro n hn
    omega
  · intro n hn
    omega

end MathlibPlus.Analysis.Claim20234
