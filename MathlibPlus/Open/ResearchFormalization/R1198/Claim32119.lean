import MathlibPlus.Open.ResearchFormalization.PrimeFibreOrbitShadowR1198

open MathlibPlus.Open.ResearchFormalization.PrimeFibreOrbitShadowR1198

namespace MathlibPlus.Open.ResearchFormalization.R1198.Claim32119

/-- Claim 32119: every split automorphism shadow on the exact finite
abelian prime-fibre carrier is a constant nonzero fibre multiplier together
with an additive character of the base. -/
def claim32119 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (H : Type*) [Fintype H] [AddCommGroup H],
    ∀ (α : (H × ZMod p) ≃+ (H × ZMod p)),
      splitGroupAutomorphismShadow α →
        ∃ e : (ZMod p)ˣ, ∃ χ : H →+ ZMod p,
          ∀ h : H, ∀ t : ZMod p,
            α (h, t) = (h, (e : ZMod p) * t + χ h)

end MathlibPlus.Open.ResearchFormalization.R1198.Claim32119
