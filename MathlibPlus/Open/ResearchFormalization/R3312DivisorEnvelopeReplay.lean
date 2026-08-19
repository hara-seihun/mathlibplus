import MathlibPlus.Open.ResearchFormalization.Q0132Claim16817

namespace MathlibPlus.Open.ResearchFormalization.R3312DivisorEnvelopeReplay

noncomputable section

open MathlibPlus.Open.ResearchFormalization.Q0132Claim16817

/-- Claim 47195: the exact divisor envelope exceeds the proposed width-two
threshold throughout the replay window, and the n=30 candidate fails at 28. -/
def divisorEnvelopeReplay_claim47195 : Prop :=
  (∀ n : ℕ, 25 ≤ n → n ≤ 1000000 → M n > n + 2) ∧
    tau 28 = 6 ∧
    shiftedDivisorValue 28 = 34 ∧
    30 + 2 = 32 ∧
    shiftedDivisorValue 28 > 30 + 2

end

end MathlibPlus.Open.ResearchFormalization.R3312DivisorEnvelopeReplay
