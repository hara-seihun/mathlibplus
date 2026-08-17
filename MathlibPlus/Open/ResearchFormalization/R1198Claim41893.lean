import MathlibPlus.Open.ResearchFormalization.PrimeFibreOrbitShadowR1198

namespace MathlibPlus.Open.ResearchFormalization.R1198Claim41893

noncomputable section

open MathlibPlus.Open.ResearchFormalization.PrimeFibreOrbitShadowR1198

/-- Claim 41893: outside the multiplier-period set, the varying affine
relative-derivative coefficient generates the whole prime fibre as one orbit. -/
def fibresOutsideMultiplierPeriodSingleDerivativeOrbit_claim41893 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (H : Type*) [Fintype H] [AddCommGroup H],
    elementarySylowP p H →
      ∀ (f : (H × ZMod p) ≃ (H × ZMod p))
        (lambda : H → (ZMod p)ˣ) (s : H → ZMod p),
        normalizedAffineProfile f lambda s →
          (∀ h : H, h ∉ multiplierPeriod lambda →
            (∃ k : H,
              lambda (h + k) ≠ lambda k ∧
                (lambda h : ZMod p)⁻¹ *
                  ((lambda (h + k) : ZMod p) - (lambda k : ZMod p)) ≠ 0) ∧
            normalizedRelativeDerivativeOrbit f (h, 0) = primeFibre h)

end

end MathlibPlus.Open.ResearchFormalization.R1198Claim41893
