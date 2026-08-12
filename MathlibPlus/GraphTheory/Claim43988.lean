import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.SetTheory.Cardinal.NatCard

namespace MathlibPlus.GraphTheory

/--
Formalization of claim 43988.  `Nat.card` expresses the cardinality of the
finite graph-isomorphism type without introducing a project-specific finite
instance for that type.
-/
theorem claim43988 {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H) :
    Nat.card (G ≃g H) = Nat.card (G ≃g G) := by
  let equiv : (G ≃g G) ≃ (G ≃g H) :=
    { toFun := fun a => a.trans e
      invFun := fun b => b.trans e.symm
      left_inv := by
        intro a
        ext v
        simp
      right_inv := by
        intro b
        ext v
        simp }
  exact Nat.card_congr equiv.symm

end MathlibPlus.GraphTheory
