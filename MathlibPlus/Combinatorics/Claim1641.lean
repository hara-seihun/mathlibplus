import Mathlib.Tactic

namespace MathlibPlus.Combinatorics.Claim1641

/-- The signed second-strip cup identity and the hook difference imply the
recurrence displayed in claim 1641. -/
theorem signedSecondStripCupRecurrence_claim1641
    (n : ℕ) (α_prev1 α_n1 α_prev2 α_n2 H_n H_n1 H_n2 : ℝ)
    (_hn : 4 ≤ n)
    (hcup : α_prev1 - α_n1 - α_prev2 + α_n2 = (-1 : ℝ) ^ n * H_n2)
    (hhook : α_n1 - α_prev1 = (-1 : ℝ) ^ n * (H_n - H_n1)) :
    α_n2 = α_prev2 + (-1 : ℝ) ^ n * (H_n - H_n1 + H_n2) := by
  nlinarith

end MathlibPlus.Combinatorics.Claim1641
