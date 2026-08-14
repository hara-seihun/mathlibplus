import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- The absorbing corner state from admitted claim 5425. -/
def claim5425_absorbingCornerState
    (R : Type*) [CommRing R] [CharZero R] : Prop :=
  ∀ (u v : R) (a : Polynomial R),
    let σ : R → R → R → R := fun X A B => X + A - B
    σ u 0 u = 0 ∧
      σ v 0 v = 0 ∧
      Polynomial.eval u a * σ u 0 u = 0 ∧
      Polynomial.eval v a * σ v 0 v = 0

end MathlibPlus.Open.ResearchFormalization
