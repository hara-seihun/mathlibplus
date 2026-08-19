import MathlibPlus.Open.ResearchFormalization.ProfileClaims

namespace MathlibPlus.Open.ResearchFormalization.ProfileOrbitClaims

open MathlibPlus.Open.ResearchFormalization.ProfileClaims

/-- Claim 38774: under the finite coprime Record-6 hypotheses, every directed
connection set invariant under the normalized derivatives is fixed by the
identity-base profile. -/
def claim_38774 : Prop :=
  ∀ {B : Type*} {H : Type*} [AddCommGroup B] [Group H]
    [Fintype B] [Fintype H],
    Nat.Coprime (Fintype.card B) (Fintype.card H) →
    ∀ (p : H → Equiv.Perm B), p 1 = Equiv.refl B →
      ∀ (S : Set (B × H)), derivativeInvariant p S →
        Set.image (identityBaseProfile p) S = S

end MathlibPlus.Open.ResearchFormalization.ProfileOrbitClaims
