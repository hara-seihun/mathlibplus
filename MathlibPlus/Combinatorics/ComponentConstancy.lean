import Mathlib.Logic.Relation

namespace MathlibPlus.Combinatorics.ComponentConstancy

/-- Claim 6552: constancy on connected components is equivalent to constancy
along adjacent source-atom pairs.  The packet's `L_f` is represented by `edge`,
and its connected-component relation by `Relation.EqvGen edge`. -/
theorem componentConstant_iff_adjacencyConstant_claim6552
    {α : Type*} (edge : α → α → Prop) (I : α → Bool) :
    (∀ a b, Relation.EqvGen edge a b → I a = I b) ↔
      (∀ a b, edge a b → I a = I b) := by
  constructor
  · intro h a b hab
    exact h a b (Relation.EqvGen.rel a b hab)
  · intro h a b hab
    induction hab with
    | rel x y hxy => exact h x y hxy
    | refl x => rfl
    | symm x y hxy ih => exact ih.symm
    | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

end MathlibPlus.Combinatorics.ComponentConstancy
