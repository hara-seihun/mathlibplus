import Mathlib

namespace MathlibPlus.Open.Groups

abbrev cyclicFourMinimumTwoGroup :=
  ZMod 4 × (ZMod 3 × (ZMod 3 × ZMod 3))

abbrev cyclicFourMinimumTwoQuotient :=
  ZMod 2 × (ZMod 3 × (ZMod 3 × ZMod 3))

abbrev G := cyclicFourMinimumTwoGroup

abbrev Q := cyclicFourMinimumTwoQuotient

def cyclicFourGenerator : G := (1, (0, (0, 0)))

def minimumTwoSubgroup : AddSubgroup G :=
  AddSubgroup.zmultiples (2 • cyclicFourGenerator)

def quotientClass (g : G) : G ⧸ minimumTwoSubgroup :=
  QuotientAddGroup.mk g

def minimumTwoBlock (g : G) : Type :=
  {x : G // quotientClass x = quotientClass g}

def cyclicFourMinimumTwoGroupAndQuotient : Prop :=
  Nat.card G = 108 ∧
    Nat.card minimumTwoSubgroup = 2 ∧
    (∀ H : AddSubgroup G, Nat.card H = 2 → H = minimumTwoSubgroup) ∧
    Nat.card (G ⧸ minimumTwoSubgroup) = 54 ∧
    (∀ g : G, Nat.card (minimumTwoBlock g) = 2) ∧
    Nonempty ((G ⧸ minimumTwoSubgroup) ≃+ Q)

end MathlibPlus.Open.Groups
