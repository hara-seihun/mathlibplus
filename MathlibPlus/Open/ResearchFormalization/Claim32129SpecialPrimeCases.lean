import MathlibPlus.Open.ResearchFormalization.PrimeFibreOrbitShadowR1198

namespace MathlibPlus.Open.ResearchFormalization.Claim32129SpecialPrimeCases

noncomputable section

open MathlibPlus.Open.ResearchFormalization.PrimeFibreOrbitShadowR1198

private def orbitShadowConclusion
    {p : ℕ} [Fact p.Prime]
    {H : Type*} [Fintype H] [AddCommGroup H]
    (f : (H × ZMod p) ≃ (H × ZMod p))
    (lambda : H → (ZMod p)ˣ) (s : H → ZMod p) : Prop :=
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

private def affineThreePointFibre : Prop :=
  ∀ σ : Equiv.Perm (ZMod 3),
    ∃ a b : ZMod 3, a ≠ 0 ∧
      ∀ x : ZMod 3, σ x = a * x + b

/-- Claim 32129: the p=2 binary-switching case and p=3 affine-fibre case
    retain the complete simultaneous orbit-shadow conclusion; constant
    multipliers and zero translations are its strict specializations. -/
def specialPrimeCases_claim32129 : Prop :=
  (∀ (H : Type*) [Fintype H] [AddCommGroup H],
    elementarySylowP 2 H →
      ∀ (f : (H × ZMod 2) ≃ (H × ZMod 2))
        (lambda : H → (ZMod 2)ˣ) (s : H → ZMod 2),
        normalizedAffineProfile f lambda s →
          orbitShadowConclusion f lambda s) ∧
    affineThreePointFibre ∧
      (∀ (p : ℕ) [Fact p.Prime]
        (H : Type*) [Fintype H] [AddCommGroup H],
        elementarySylowP p H →
          ∀ (f : (H × ZMod p) ≃ (H × ZMod p))
            (lambda : H → (ZMod p)ˣ) (s : H → ZMod p),
            normalizedAffineProfile f lambda s →
              (∀ h : H, lambda h = lambda 0) →
                orbitShadowConclusion f lambda s) ∧
        (∀ (p : ℕ) [Fact p.Prime]
          (H : Type*) [Fintype H] [AddCommGroup H],
          elementarySylowP p H →
            ∀ (f : (H × ZMod p) ≃ (H × ZMod p))
              (lambda : H → (ZMod p)ˣ) (s : H → ZMod p),
              normalizedAffineProfile f lambda s →
                (∀ h : H, s h = 0) →
                  orbitShadowConclusion f lambda s)

end

end MathlibPlus.Open.ResearchFormalization.Claim32129SpecialPrimeCases
