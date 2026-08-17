import MathlibPlus.Open.Analysis.FirstLaguerreDivisorChannels

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.FirstLaguerreHermitianMatrix15057

noncomputable section

open FirstLaguerreDivisorChannels

/-- Claim 15057: the exact channel-kernel Fourier entry, Hermitian matrix,
and reflected real-side kernel identity for the fixed divisor/complement
channels. -/
def claim15057 : Prop :=
  ∀ q : ℕ, 2 ≤ q →
    channelTransformAgreement q ∧
      (∀ (i j : Fin 2) (x : ℝ),
        channelKernelFourier q i j x =
          (1 / 8 : ℂ) *
            (2 * star (deriv (channelTransform q i) x) *
                deriv (channelTransform q j) x -
              star (iteratedDeriv 2 (channelTransform q i) x) *
                channelTransform q j x -
              star (channelTransform q i x) *
                iteratedDeriv 2 (channelTransform q j) x)) ∧
        (∀ x : ℝ,
          Matrix.IsHermitian (channelFourierMatrix q x)) ∧
        (∀ (i j : Fin 2) (y : ℝ),
          channelKernel q j i (-y) = channelKernel q i j y)

end

end MathlibPlus.Open.Analysis.FirstLaguerreHermitianMatrix15057
