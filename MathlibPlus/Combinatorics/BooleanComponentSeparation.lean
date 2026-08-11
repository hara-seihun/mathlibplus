import Mathlib

/-!
# Boolean separation of connected components

Formalization of admitted claim 9452.  The edge relation generates connected
components through `Relation.EqvGen`; a coloring is component-constant exactly
when it is constant along that equivalence relation.
-/

namespace MathlibPlus.Combinatorics.BooleanComponentSeparation

/-- Two vertices of a finite constraint graph are in different components iff a
component-constant Boolean coloring separates them. -/
theorem boolean_separation
    (α : Type) [Fintype α] (edge : α → α → Prop) (x y : α) :
    ¬ Relation.EqvGen edge x y ↔
      ∃ color : α → Bool,
        color x ≠ color y ∧
          ∀ a b, Relation.EqvGen edge a b → color a = color b := by
  classical
  constructor
  · intro hxy
    let color : α → Bool := fun z =>
      if Relation.EqvGen edge x z then true else false
    refine ⟨color, ?_, ?_⟩
    · have hxx : Relation.EqvGen edge x x := Relation.EqvGen.refl x
      simp [color, hxx, hxy]
    · intro a b hab
      by_cases hxa : Relation.EqvGen edge x a
      · have hxb : Relation.EqvGen edge x b :=
          Relation.EqvGen.trans x a b hxa hab
        simp [color, hxa, hxb]
      · have hxb : ¬ Relation.EqvGen edge x b := by
          intro hxb
          apply hxa
          exact Relation.EqvGen.trans x b a hxb (Relation.EqvGen.symm a b hab)
        simp [color, hxa, hxb]
  · rintro ⟨color, hne, hconstant⟩ hxy
    exact hne (hconstant x y hxy)

end MathlibPlus.Combinatorics.BooleanComponentSeparation
