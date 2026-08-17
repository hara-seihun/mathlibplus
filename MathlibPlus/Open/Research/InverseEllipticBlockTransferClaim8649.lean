import MathlibPlus.Open.Research.ScaleFreeTwoDirectionEstimate

namespace MathlibPlus.Open.Research

/-- The inverse-direction elliptic-block estimate with the endpoint ratio in the
same transfer carrier as the forward estimate. -/
def inverseEllipticBlockTransferBoundClaim8649 : Prop :=
  ∀ (a : ℕ → ℝ) (x ρ : ℝ) (A B : ℕ),
    0 ≤ ρ →
    ρ < 1 →
    (∀ j, 0 < a j) →
    A ≤ B →
    ellipticBlockCondition a x ρ A B →
    let T := zeroDiagonalTransferProduct a x A (B - A)
    twoOperatorNorm (T⁻¹) ^ 2 ≤
      ((1 + ρ) / (1 - ρ)) *
        (a (B + 1) / a A) *
        Real.exp (((1 + ρ ^ 2) / (1 - ρ ^ 2)) *
          logarithmicTotalVariation a A B)

end MathlibPlus.Open.Research
