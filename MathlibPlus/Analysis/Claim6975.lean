import Mathlib

namespace MathlibPlus.Analysis.Claim6975

/-- The normalized first-jet moment formulas from claim 6975, with the
source's integral definition retained as the displayed hypotheses. -/
theorem normalized_first_jet_moments_claim6975
    {K : Type*} [Field K] [CharZero K]
    (s k : K) (I00 I10 I11 I20 : ℕ → K)
    (h00 : ∀ n, I00 n ≠ 0)
    (h10 : ∀ n, I10 n = I00 n * ((1 - s) / 2))
    (h11 : ∀ n, I11 n = I00 n * ((s ^ 2 - s + k) / 4))
    (h20 : ∀ n, I20 n = I00 n * ((s ^ 2 - 3 * s - k + 2) / 4)) :
    ∀ n, I10 n / I00 n = (1 - s) / 2 ∧
      I11 n / I00 n = (s ^ 2 - s + k) / 4 ∧
      I20 n / I00 n = (s ^ 2 - 3 * s - k + 2) / 4 := by
  intro n
  rw [h10 n, h11 n, h20 n]
  field_simp [h00 n]
  simp

end MathlibPlus.Analysis.Claim6975
