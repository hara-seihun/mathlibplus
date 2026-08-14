import Mathlib

namespace MathlibPlus.Open.Algebra

/-- A unital multiplication is directly finite when every left inverse is a right inverse. -/
def DirectlyFinite (R : Type*) [MulOneClass R] : Prop :=
  ∀ a b : R, a * b = 1 → b * a = 1

/-- Every group ring over a characteristic-zero field is directly finite. -/
def characteristicZeroGroupRingsAreDirectlyFinite : Prop :=
  ∀ (G K : Type*) [Group G] [Field K] [CharZero K],
    DirectlyFinite (MonoidAlgebra K G)

end MathlibPlus.Open.Algebra
