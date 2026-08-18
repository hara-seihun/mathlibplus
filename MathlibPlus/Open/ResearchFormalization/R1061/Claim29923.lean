import MathlibPlus.Open.ResearchFormalization.R1061.Claim29924

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1061.Claim29923

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1061.Claim29924

/-- The gap-at-least-two Vieta obstruction for the denominator root packet. -/
def claim29923_vietaObstructionGapAtLeastTwo : Prop :=
  ∀ {p q : ℕ} {δ : ℚ},
    0 < p →
      p < q →
        2 ≤ q - p →
          δ ≠ 0 →
            δ ≠ (p : ℚ) →
              δ ≠ (q : ℚ) →
                ∀ packet : PositiveRootPacket p q δ,
                  (∃ base : Fin q,
                      packet.roots base = 1 ∧
                        (∀ i, packet.roots i = 1 → i = base) ∧
                          (∀ i, i ≠ base → ∃ r : ℚ, packet.roots i = r ^ 2)) →
                    (denominatorPolynomial p q δ).coeff (q - 1) = 0 ∧
                      elementarySymmetricStatistic packet.roots 1 = 0 ∧
                        (-δ * ((q : ℚ) - (p : ℚ))) ≠ 0 ∧
                          ¬ (∀ i, 0 < packet.roots i)

end

end MathlibPlus.Open.ResearchFormalization.R1061.Claim29923
