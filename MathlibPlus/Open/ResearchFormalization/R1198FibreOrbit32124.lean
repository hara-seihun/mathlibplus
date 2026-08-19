import MathlibPlus.Open.ResearchFormalization.PrimeFibreOrbitShadowR1198

namespace MathlibPlus.Open.ResearchFormalization.R1198FibreOrbit32124

open MathlibPlus.Open.ResearchFormalization.PrimeFibreOrbitShadowR1198

noncomputable section

/-- Claim 32124: in the multiplier-period subgroup but outside the additive
locus, a violating period shift produces a nonzero translation on the fibre,
so that fibre is one normalized-relative-derivative orbit. -/
def claim32124 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (H : Type*) [Fintype H] [AddCommGroup H],
    elementarySylowP p H →
      ∀ (f : (H × ZMod p) ≃ (H × ZMod p))
        (lambda : H → (ZMod p)ˣ) (s : H → ZMod p),
        normalizedAffineProfile f lambda s →
          ∀ h : H,
            h ∈ multiplierPeriod lambda →
              h ∉ additiveLocus lambda s →
                ∃ k : H, ∃ c : ZMod p,
                  k ∈ multiplierPeriod lambda ∧
                    c ≠ 0 ∧
                    s (h + k) ≠ s h + s k ∧
                    (∀ t : ZMod p,
                      normalizedRelativeDerivative f (k, 0) (h, t) =
                        (h, t + c)) ∧
                    normalizedRelativeDerivativeOrbit f (h, 0) =
                      primeFibre h

end

end MathlibPlus.Open.ResearchFormalization.R1198FibreOrbit32124
