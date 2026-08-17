import MathlibPlus.Open.ResearchFormalization.PrimeFibreOrbitShadowR1198

namespace MathlibPlus.Open.ResearchFormalization.R1198Claim41895

open MathlibPlus.Open.ResearchFormalization.PrimeFibreOrbitShadowR1198

noncomputable section

/-- Claim 41895: outside the additive locus but inside the multiplier-period
subgroup, a failed additivity relation supplies a nonzero fibre translation,
so the complete fibre is one normalized-relative-derivative orbit. -/
def claim41895 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (H : Type*) [Fintype H] [AddCommGroup H],
    elementarySylowP p H →
      ∀ (f : (H × ZMod p) ≃ (H × ZMod p))
        (lambda : H → (ZMod p)ˣ) (s : H → ZMod p),
        normalizedAffineProfile f lambda s →
          ∀ h : H,
            h ∈ multiplierPeriod lambda →
              h ∉ additiveLocus lambda s →
                ∃ k : H,
                  k ∈ multiplierPeriod lambda ∧
                    s (h + k) ≠ s h + s k ∧
                    normalizedRelativeDerivativeOrbit f (h, 0) =
                      primeFibre h

end

end MathlibPlus.Open.ResearchFormalization.R1198Claim41895
