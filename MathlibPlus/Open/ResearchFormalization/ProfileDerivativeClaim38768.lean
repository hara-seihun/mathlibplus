import MathlibPlus.Open.ResearchFormalization.ProfileClaims

namespace MathlibPlus.Open.ResearchFormalization.ProfileDerivativeClaims

open MathlibPlus.Open.ResearchFormalization.ProfileClaims

/-- Claim 38768: the normalized derivative has the stated fibre formula, and
its invariant-section identity uses the multiplicative `(t,k)` indices. -/
def claim_38768 : Prop :=
  ∀ {B : Type*} {H : Type*} [AddCommGroup B] [Group H]
    (p : H → Equiv.Perm B), p 1 = Equiv.refl B →
    (∀ (a : H) (u v : B) (h : H),
      normalizedRelativeDerivative p a u (v, h) =
        (((p h)⁻¹) (p (h * a) (v + u) - p a u), h)) ∧
      (∀ (S : Set (B × H)) (a : H), derivativeInvariant p S →
        let X := fiberSection S a
        ∀ (t : B) (k : H),
          imageSet (p (a * k)) (translateSet X t) =
            translateSet (imageSet (p a) X) (p k t))

end MathlibPlus.Open.ResearchFormalization.ProfileDerivativeClaims
