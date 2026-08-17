import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0983.Claim27898

noncomputable section

private def displacementSubgroup
    (B : Type*) [AddCommGroup B] (p : Equiv.Perm B) : AddSubgroup B :=
  AddSubgroup.closure (Set.range (fun t : B => t - p t + p 0))

private def qZero {B : Type*} [AddGroup B]
    (p : Equiv.Perm B) (x : B) : B :=
  p.symm (x - p 0)

/-- Claim 27898: on the additive quotient by the exact displacement
subgroup, the special map `Q₀ = p⁻¹ τ₋c` translates by `-2 c̄`, while `p`
translates by `c̄`. -/
def claim27898 : Prop :=
  ∀ (B : Type*) [Fintype B] [AddCommGroup B],
    Odd (Fintype.card B) →
      ∀ p : Equiv.Perm B,
        let c := p 0
        let W := displacementSubgroup B p
        (∀ x : B,
          QuotientAddGroup.mk' W (qZero p x) =
            QuotientAddGroup.mk' W x -
              (QuotientAddGroup.mk' W c + QuotientAddGroup.mk' W c)) ∧
          (∀ x : B,
            QuotientAddGroup.mk' W (p x) =
              QuotientAddGroup.mk' W x + QuotientAddGroup.mk' W c)

end

end MathlibPlus.Open.ResearchFormalization.R0983.Claim27898
