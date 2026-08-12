import Mathlib

namespace MathlibPlus.Combinatorics.Claim26078

/-- For a finite forest edge state, binary colorings of generated components
are equivalent to reachable-constant vertex colorings and then to
edge-constant vertex colorings.  The displayed support and edge-partition
identities make the claimed preservation explicit. -/
theorem componentColoringAndEdgeConstancy
    {V : Type*} [Fintype V] (G : SimpleGraph V) (_hforest : G.IsAcyclic) :
    let r : Setoid V := Relation.EqvGen.setoid G.Adj
    let componentOf : V → Quotient r := Quotient.mk r
    let Reachable :=
      {c : V → Bool // ∀ a b, Relation.EqvGen G.Adj a b → c a = c b}
    let Edgewise :=
      {c : V → Bool // ∀ a b, G.Adj a b → c a = c b}
    let support : (V → Bool) → Bool → Set V := fun c b => {x | c x = b}
    let edgePart : (V → Bool) → Bool → Set (V × V) :=
      fun c b => {p | G.Adj p.1 p.2 ∧ c p.1 = b ∧ c p.2 = b}
    ∃ componentColoring : (Quotient r → Bool) ≃ Reachable,
      ∃ edgeColoring : Reachable ≃ Edgewise,
        (∀ q b, support (componentColoring q).1 b =
          {x | q (componentOf x) = b}) ∧
        (∀ c b, support (edgeColoring c).1 b = support c.1 b) ∧
        (∀ c b, edgePart (edgeColoring c).1 b = edgePart c.1 b) := by
  classical
  dsimp
  let r : Setoid V := Relation.EqvGen.setoid G.Adj
  let componentOf : V → Quotient r := Quotient.mk r
  let Reachable :=
    {c : V → Bool // ∀ a b, Relation.EqvGen G.Adj a b → c a = c b}
  let Edgewise :=
    {c : V → Bool // ∀ a b, G.Adj a b → c a = c b}
  let support : (V → Bool) → Bool → Set V := fun c b => {x | c x = b}
  let edgePart : (V → Bool) → Bool → Set (V × V) :=
    fun c b => {p | G.Adj p.1 p.2 ∧ c p.1 = b ∧ c p.2 = b}
  let componentColoring : (Quotient r → Bool) ≃ Reachable :=
    { toFun := fun q =>
        ⟨fun x => q (componentOf x), by
          intro a b hab
          exact congrArg q (@Quotient.sound V r a b hab)⟩
      invFun := fun c =>
        Quotient.lift c.1 (by
          intro a b hab
          exact c.2 a b hab)
      left_inv := by
        intro q
        funext z
        refine Quotient.inductionOn z ?_
        intro x
        rfl
      right_inv := by
        intro c
        apply Subtype.ext
        funext x
        rfl }
  let edgeColoring : Reachable ≃ Edgewise :=
    { toFun := fun c =>
        ⟨c.1, by
          intro a b hab
          exact c.2 a b (Relation.EqvGen.rel a b hab)⟩
      invFun := fun c =>
        ⟨c.1, by
          intro a b hab
          induction hab with
          | rel x y hxy => exact c.2 x y hxy
          | refl x => rfl
          | symm x y hxy ih => exact ih.symm
          | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz⟩
      left_inv := by
        intro c
        apply Subtype.ext
        rfl
      right_inv := by
        intro c
        apply Subtype.ext
        rfl }
  refine ⟨componentColoring, edgeColoring, ?_, ?_, ?_⟩
  · intro q b
    rfl
  · intro c b
    rfl
  · intro c b
    rfl

end MathlibPlus.Combinatorics.Claim26078
