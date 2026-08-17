import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.CayleyPeriod

noncomputable section

attribute [local instance] Classical.decEq

/-- The left translate `xU` of a connection set. -/
def leftNeighborhood {G : Type*} [Group G]
    (U : Set G) (x : G) : Set G :=
  Set.image (fun u : G => x * u) U

/-- The left-period set of a connection set. -/
def periodSet {G : Type*} [Group G] (U : Set G) : Set G :=
  {a | leftNeighborhood U a = U}

/-- A proposition expressing that the period set is the carrier of a
subgroup. -/
def periodIsSubgroup {G : Type*} [Group G] (U : Set G) : Prop :=
  ∃ H : Subgroup G, (H : Set G) = periodSet U

/-- The open and closed left-neighborhood predicates for the Cayley relation. -/
def noDistinctEqualNeighborhoods {G : Type*} [Group G]
    (neighborhood : G → Set G) : Prop :=
  ∀ x y : G, x ≠ y → neighborhood x ≠ neighborhood y

def claim61110 : Prop :=
  ∀ (G : Type*) [Group G] (U : Set G),
    periodIsSubgroup U ∧
      (∀ x y : G,
        leftNeighborhood U x = leftNeighborhood U y ↔
          y⁻¹ * x ∈ periodSet U) ∧
      ((noDistinctEqualNeighborhoods (leftNeighborhood U)) ↔
        periodSet U = ({(1 : G)} : Set G)) ∧
      ((noDistinctEqualNeighborhoods
          (leftNeighborhood (insert (1 : G) U))) ↔
        periodSet (insert (1 : G) U) = ({(1 : G)} : Set G))

end
end MathlibPlus.Open.ResearchFormalization.CayleyPeriod
