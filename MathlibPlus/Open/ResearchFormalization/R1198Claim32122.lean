import MathlibPlus.Open.ResearchFormalization.PrimeFibreOrbitShadowR1198

namespace MathlibPlus.Open.ResearchFormalization.R1198

noncomputable section

open MathlibPlus.Open.ResearchFormalization.PrimeFibreOrbitShadowR1198

/-- Claim 32122: outside the multiplier-period subgroup, a nonzero affine
coefficient in the relative derivative generates the whole prime fibre. -/
def claim32122 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (H : Type*) [Fintype H] [AddCommGroup H],
    elementarySylowP p H →
    ∀ (f : (H × ZMod p) ≃ (H × ZMod p))
      (lambda : H → (ZMod p)ˣ) (s : H → ZMod p),
      normalizedAffineProfile f lambda s →
      (∀ (h k : H) (m t : ZMod p),
        normalizedRelativeDerivative f (k, m) (h, t) =
          (h,
            (lambda h : ZMod p)⁻¹ * (lambda (h + k) : ZMod p) * t +
              (lambda h : ZMod p)⁻¹ *
                ((lambda (h + k) : ZMod p) - (lambda k : ZMod p)) * m +
              (lambda h : ZMod p)⁻¹ *
                (s (h + k) - s k - s h))) ∧
      (∀ h : H, h ∉ multiplierPeriod lambda →
        (∃ k : H, lambda (h + k) ≠ lambda k) ∧
        normalizedRelativeDerivativeOrbit f (h, 0) = primeFibre h)

end
end MathlibPlus.Open.ResearchFormalization.R1198
