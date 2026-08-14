import Mathlib

namespace MathlibPlus.Open

universe uR uI uC1 uC3

section

/--
For a finite coordinate module, coordinatewise boundary certificates imply
exactness at the coordinate module, under the cochain condition.
-/
def finiteCoordinateBoundaryExactness
    (R : Type uR) (I : Type uI) (C1 : Type uC1) (C3 : Type uC3)
    [Ring R] [Fintype I]
    [AddCommGroup C1] [AddCommGroup C3]
    [Module R C1] [Module R C3]
    (d1 : C1 →ₗ[R] (I → R))
    (d2 : (I → R) →ₗ[R] C3) : Prop :=
  letI := Classical.decEq I
  d2.comp d1 = 0 →
    (∀ i : I, ∃ xi : C1, d1 xi = (Pi.single i (1 : R) : I → R)) →
      ∀ y : I → R, d2 y = 0 → ∃ x : C1, d1 x = y

end

end MathlibPlus.Open
