import MathlibPlus.Basic

namespace MathlibPlus.GroupTheory

/-!
Formalization of admitted claim 42028.  A regular abelian permutation group is
represented by the translations of an additive commutative group `B`.  The
left side is exactly commutation with every translation, and the right side
says that the permutation is translation by `f 0`.
-/

/-- The centralizer of the regular translation action of an abelian group. -/
theorem regularAbelianCentralizer
    {B : Type*} [AddCommGroup B] (f : Equiv.Perm B) :
    (∀ a x : B, f (a + x) = a + f x) ↔
      (∀ x : B, f x = x + f 0) := by
  constructor
  · intro h x
    simpa using h x 0
  · intro h a x
    calc
      f (a + x) = (a + x) + f 0 := h _
      _ = a + (x + f 0) := by rw [add_assoc]
      _ = a + f x := by rw [h x]

end MathlibPlus.GroupTheory
