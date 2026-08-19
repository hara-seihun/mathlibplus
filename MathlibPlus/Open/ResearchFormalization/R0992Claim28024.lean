import MathlibPlus.Open.ResearchFormalization.R0992Claim28032

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0992Claim28024

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R0992Claim28032
open MathlibPlus.Open.Research.OrbitalCriteria

private abbrev MonomialDirection :=
  Fin 3 × (Fin 3 × (Fin 3 × {e : F3 // e ≠ 0}))

private def monomialTable
    (u v ξ : Fin 3) (ε : F3) : Plane → Fibre :=
  fun x j =>
    if j = ξ then ε * (x 0) ^ u.val * (x 1) ^ v.val else 0

private def monomialTableOf (d : MonomialDirection) : Plane → Fibre :=
  monomialTable d.1 d.2.1 d.2.2.1 d.2.2.2.1

private def monomialTransporter (d : MonomialDirection) : Equiv.Perm E :=
  transporter (monomialTableOf d)

private def monomialGroup (d : MonomialDirection) :
    Subgroup (Equiv.Perm E) :=
  generatedGroup (monomialTransporter d)

private def exactTwoClosure (d : MonomialDirection) : Set (Equiv.Perm E) :=
  twoClosureOf (monomialGroup d : Set (Equiv.Perm E))

private def conjugatesRegularPair (d : MonomialDirection) : Prop :=
  ∃ c : Equiv.Perm E,
    c ∈ exactTwoClosure d ∧
      Set.image (fun h : Equiv.Perm E => c⁻¹ * h * c)
        (translationGroup : Set (Equiv.Perm E)) =
        transportedTranslations (monomialTransporter d)

/-- Claim 28024: every scalar monomial direction on each of the three fibre
    coordinates has its displayed regular pair conjugate inside the exact
    two-closure, and the complete direction census is `3·3·3·2 = 54`. -/
def monomialBasisTwists_claim28024 : Prop :=
  (Finset.univ : Finset MonomialDirection).card = 54 ∧
    ∀ d : MonomialDirection, conjugatesRegularPair d

end

end MathlibPlus.Open.ResearchFormalization.R0992Claim28024
