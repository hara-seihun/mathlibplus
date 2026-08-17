import MathlibPlus.Open.ResearchFormalization.PrimeFibreOrbitShadowR1198

namespace MathlibPlus.Open.ResearchFormalization.R1198AdditiveLocus32123

/-- Claim 32123: in the exact normalized prime-fibre context, the additive
locus is the carrier of an additive subgroup inside the multiplier-period
subgroup, and the translation profile restricts to an additive homomorphism. -/
def claim32123 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (H : Type*) [Fintype H] [AddCommGroup H],
    MathlibPlus.Open.ResearchFormalization.PrimeFibreOrbitShadowR1198.elementarySylowP
        p H →
      ∀ (f : (H × ZMod p) ≃ (H × ZMod p))
        (lambda : H → (ZMod p)ˣ) (s : H → ZMod p),
        MathlibPlus.Open.ResearchFormalization.PrimeFibreOrbitShadowR1198.normalizedAffineProfile
          f lambda s →
          ∃ L : AddSubgroup H,
            (∀ h : H,
              h ∈ L ↔
                h ∈ MathlibPlus.Open.ResearchFormalization.PrimeFibreOrbitShadowR1198.additiveLocus
                  lambda s) ∧
            (∀ h : H, h ∈ L →
              h ∈ MathlibPlus.Open.ResearchFormalization.PrimeFibreOrbitShadowR1198.multiplierPeriod
                lambda) ∧
            ∃ φ : L →+ ZMod p, ∀ h : L, φ h = s h.1

end MathlibPlus.Open.ResearchFormalization.R1198AdditiveLocus32123
