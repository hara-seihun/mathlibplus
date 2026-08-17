import MathlibPlus.Open.Research.ScaleFreeTwoDirectionEstimate

namespace MathlibPlus.Open.Research.FormalizationBatch.K0109Claim8648

open MathlibPlus.Open.Research

/-- The forward elliptic-block transfer estimate with the endpoint ratio and
exact logarithmic-motion constant. -/
def forwardEllipticBlockTransferBound_claim8648 : Prop :=
  ∀ (a : ℕ → ℝ) (x ρ : ℝ) (A B : ℕ),
    0 ≤ ρ →
    ρ < 1 →
    (∀ j : ℕ, 0 < a j) →
    A ≤ B →
    ellipticBlockCondition a x ρ A B →
    twoOperatorNorm
        (zeroDiagonalTransferProduct a x A (B - A)) ^ 2 ≤
      ((1 + ρ) / (1 - ρ)) *
        (a A / a (B + 1)) *
        Real.exp
          (((1 + ρ ^ 2) / (1 - ρ ^ 2)) *
            logarithmicTotalVariation a A B)

end MathlibPlus.Open.Research.FormalizationBatch.K0109Claim8648
