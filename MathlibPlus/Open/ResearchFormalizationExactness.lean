import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationExactness

/-- Claim 59916: triangular local certificates force exactness at the middle term. -/
def awdtUnitriangularReciprocityCertificateExactness : Prop :=
  ∀ {R I COne CThree : Type*}
    [CommRing R] [Fintype I] [LinearOrder I]
    [AddCommGroup COne] [AddCommGroup CThree]
    [Module R COne] [Module R CThree]
    (d1 : COne →ₗ[R] (I → R))
    (d2 : (I → R) →ₗ[R] CThree),
    d2.comp d1 = 0 →
    (∀ i : I, ∃ certificate : COne,
      (d1 certificate) i = 1 ∧
        ∀ j : I, i < j → (d1 certificate) j = 0) →
    ∀ y : I → R, d2 y = 0 ↔ ∃ x : COne, d1 x = y

end MathlibPlus.Open.ResearchFormalizationExactness
