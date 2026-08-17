import MathlibPlus.Open.NumberTheory.Claim8251

namespace MathlibPlus.Open.Research.FormalizationBatch.K0077Claim8253

open Classical
open MathlibPlus.Open.NumberTheory.Claim8251

/-- The q-power indicator and both endpoint evaluations at t equal to zero. -/
def endpointQPowerIndicator_claim8253 : Prop :=
  ∀ (q a : ℕ),
    q.Prime →
    1 ≤ a →
    (∀ n : ℕ, 1 ≤ n →
      generalizedJordanCoefficient q 0 n =
        if ∃ k : ℕ, n = q ^ k then 1 else 0) ∧
      summatoryGeneralizedJordan q 0 (q ^ a) = (a + 1 : ℝ) ∧
      outerPrimePowerResiduePacket q a 1 =
        Complex.ofReal (-(a + 1 : ℝ))

end MathlibPlus.Open.Research.FormalizationBatch.K0077Claim8253
