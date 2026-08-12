import MathlibPlus.Basic

namespace MathlibPlus.Algebra

/-- The additive expansion of a sesquilinear bracket in both arguments. -/
theorem sesquilinear_add_add_expansion_claim4862
    {M G : Type*} [AddCommMonoid M] [AddCommMonoid G]
    (B : M →+ M →+ G) (F F' H H' : M) :
    B (F + F') (H + H') =
      B F H + B F H' + B F' H + B F' H' := by
  simp only [map_add, AddMonoidHom.add_apply]
  abel

/-- The quadratic specialization of the additive expansion in claim 4862. -/
theorem quadratic_add_expansion_claim4862
    {M G : Type*} [AddCommMonoid M] [AddCommMonoid G]
    (B : M →+ M →+ G) (F H : M) :
    B (F + H) (F + H) =
      B F F + B F H + B H F + B H H := by
  exact sesquilinear_add_add_expansion_claim4862 B F H F H

end MathlibPlus.Algebra
