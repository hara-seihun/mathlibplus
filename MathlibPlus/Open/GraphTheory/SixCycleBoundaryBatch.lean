import Mathlib

namespace MathlibPlus.Open.GroupTheory.SixCycleBatch

abbrev BoundaryVertex := ZMod 3 × ZMod 2

/-- The orbit of a point under a permutation subgroup. -/
def permutationOrbit (H : Subgroup (Equiv.Perm BoundaryVertex))
    (x : BoundaryVertex) : Set BoundaryVertex :=
  {y | ∃ h : H, h.1 x = y}

/-- Regularity for a finite permutation subgroup. -/
def RegularPermutationSubgroup
    (H : Subgroup (Equiv.Perm BoundaryVertex)) : Prop :=
  (∀ x y : BoundaryVertex, ∃ h : H, h.1 x = y) ∧
  (∀ h : H, ∀ x : BoundaryVertex, h.1 x = x → h = 1)

/-- Claim 31468: the displayed six-cycle in the full symmetric group has a
regular cyclic subgroup whose order-three subgroup crosses the coordinate
fibres. -/
def claim31468 : Prop :=
  ∃ c : Equiv.Perm BoundaryVertex,
    c (0, 0) = (1, 0) ∧
    c (1, 0) = (2, 1) ∧
    c (2, 1) = (0, 1) ∧
    c (0, 1) = (1, 1) ∧
    c (1, 1) = (2, 0) ∧
    c (2, 0) = (0, 0) ∧
    let C := Subgroup.closure ({c} : Set (Equiv.Perm BoundaryVertex))
    let C3 := Subgroup.closure ({c ^ 2} : Set (Equiv.Perm BoundaryVertex))
    Nat.card C = 6 ∧
    RegularPermutationSubgroup C ∧
    Nat.card C3 = 3 ∧
    (∀ H : Subgroup (Equiv.Perm BoundaryVertex),
      Nat.card H = 3 → H ≤ C → H = C3) ∧
    permutationOrbit C3 (0, 0) =
      {(0, 0), (1, 1), (2, 1)}

end MathlibPlus.Open.GroupTheory.SixCycleBatch
