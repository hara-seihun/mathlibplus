import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The pendant split functional equation in the arm-affine same-stratum sector. -/
def pendantSplitFunctionalEquation : Prop :=
  ∀ {R : Type*} [CommRing R] [CharZero R]
    (F : R → R → R → R → R) (f α β : R → R),
    (∀ X A B M,
      F X A B M =
        f X + α X * (A - B) + β X * (A - M)) →
      let PF : R → R → R := fun u v =>
        F u 0 u v + F v 0 v u
      let g : R → R := fun X => f X - X * α X
      (∀ u v, PF u v = 0) ↔
        (∀ u v, g u + g v = v * β u + u * β v)

end MathlibPlus.Open.Analysis
