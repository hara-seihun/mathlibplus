import MathlibPlus.Open.ResearchFormalization.PrimeFibreOrbitShadowR1198

namespace MathlibPlus.Open.ResearchFormalization.R1198Claim41897

open MathlibPlus.Open.ResearchFormalization.PrimeFibreOrbitShadowR1198

/-- Claim 41897: under the exact normalized affine prime-fibre context, the
relative-derivative orbit partition is shadowed by a split affine group
automorphism, with pointwise agreement on the additive locus and whole-fibre
orbits away from it. -/
def affinePrimeFibreOrbitShadow_41897 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (H : Type*) [Fintype H] [AddCommGroup H],
    elementarySylowP p H →
      ∀ (f : (H × ZMod p) ≃ (H × ZMod p))
        (lambda : H → (ZMod p)ˣ) (s : H → ZMod p),
        normalizedAffineProfile f lambda s →
          ∃ e : (ZMod p)ˣ, ∃ χ : H →+ ZMod p,
            ∃ α : (H × ZMod p) ≃+ (H × ZMod p),
              e = lambda 0 ∧
              (∀ h : H, ∀ t : ZMod p,
                α (h, t) = (h, (e : ZMod p) * t + χ h)) ∧
              (∀ x : H × ZMod p,
                Set.image (fun y => α y)
                    (normalizedRelativeDerivativeOrbit f x) =
                  Set.image f (normalizedRelativeDerivativeOrbit f x)) ∧
              (∀ h : H, h ∈ additiveLocus lambda s →
                ∀ t : ZMod p, α (h, t) = f (h, t)) ∧
              (∀ h : H, h ∉ additiveLocus lambda s →
                normalizedRelativeDerivativeOrbit f (h, 0) = primeFibre h ∧
                Set.image f (primeFibre h) = primeFibre h ∧
                Set.image (fun y => α y) (primeFibre h) = primeFibre h)

end MathlibPlus.Open.ResearchFormalization.R1198Claim41897
