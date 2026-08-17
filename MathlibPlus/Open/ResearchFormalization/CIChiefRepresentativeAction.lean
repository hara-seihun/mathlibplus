import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.CIChiefRepresentativeAction

/-- Claim 61158: quotient-equal representatives induce the same conjugation
on an abelian normal subgroup.  The premise is written in the equivalent
`x⁻¹ y ∈ A` form from the source statement. -/
def abelianNormalRepresentativeAction_claim61158 : Prop :=
  ∀ (G : Type*) [Group G] (A : Subgroup G),
    (∀ a b : G, a ∈ A → b ∈ A → a * b = b * a) →
    A.Normal →
      ∀ (x y : G), x⁻¹ * y ∈ A →
        ∀ a : G, a ∈ A →
          x * a * x⁻¹ = y * a * y⁻¹

end MathlibPlus.Open.ResearchFormalization.CIChiefRepresentativeAction
