import Mathlib

namespace MathlibPlus.Open.Combinatorics

abbrev ResidualGroup60097 := ZMod 4 × (Fin 3 → ZMod 3)
abbrev ResidualFiber60097 := Fin 3 → ZMod 3

def identityFree60097 (R : Set ResidualGroup60097) : Prop :=
  (0 : ResidualGroup60097) ∉ R

def inverseClosed60097 (R : Set ResidualGroup60097) : Prop :=
  ∀ ⦃x : ResidualGroup60097⦄, x ∈ R → -x ∈ R

def cayleyAdjacency60097 (R : Set ResidualGroup60097)
    (x y : ResidualGroup60097) : Prop :=
  x ≠ y ∧ y - x ∈ R

def graphIsomorphism60097 (R T : Set ResidualGroup60097)
    (f : ResidualGroup60097 → ResidualGroup60097) : Prop :=
  Function.Bijective f ∧
    ∀ x y,
      (cayleyAdjacency60097 R x y ↔ cayleyAdjacency60097 T (f x) (f y))

def ordinaryUndirectedCI60097 (R : Set ResidualGroup60097) : Prop :=
  identityFree60097 R ∧
    inverseClosed60097 R ∧
    ∀ T : Set ResidualGroup60097,
      identityFree60097 T →
      inverseClosed60097 T →
      ∀ f : ResidualGroup60097 → ResidualGroup60097,
        graphIsomorphism60097 R T f →
        ∃ α : ResidualGroup60097 ≃+ ResidualGroup60097,
          Set.image (fun x => α x) R = T

def quotientCayleyAdjacency60097 (W : Submodule (ZMod 3) ResidualFiber60097)
    (x y : ResidualFiber60097) : Prop :=
  x ≠ y ∧ y - x ∈ ((W : Set ResidualFiber60097) \ {0})

def closedNeighborhood60097 (W : Submodule (ZMod 3) ResidualFiber60097)
    (x : ResidualFiber60097) : Set ResidualFiber60097 :=
  {z | z = x ∨ quotientCayleyAdjacency60097 W x z}

def trueTwin60097 (W : Submodule (ZMod 3) ResidualFiber60097)
    (x y : ResidualFiber60097) : Prop :=
  x ≠ y ∧ closedNeighborhood60097 W x = closedNeighborhood60097 W y

/-- Exact formal statement of the admitted residual-subgroup claim. -/
def ciMixedAbelianResidualSubgroupCosetClaim60097 : Prop :=
  (∀ H : AddSubgroup ResidualGroup60097,
      ordinaryUndirectedCI60097 ((H : Set ResidualGroup60097) \ {0}) ∧
      ordinaryUndirectedCI60097 (Set.univ \ (H : Set ResidualGroup60097))) ∧
    Fintype.card (AddSubgroup ResidualGroup60097) = 84 ∧
    (∀ W : Submodule (ZMod 3) ResidualFiber60097,
      (ordinaryUndirectedCI60097
          ((((Set.univ : Set (ZMod 4)) \ {0}) ×ˢ ({0} : Set ResidualFiber60097)) ∪
            (Set.univ ×ˢ ((W : Set ResidualFiber60097) \ {0}))) ∧
        (((Set.univ : Set (ZMod 4)) \ {0}) ×ˢ ({0} : Set ResidualFiber60097)) ∪
            (Set.univ ×ˢ ((W : Set ResidualFiber60097) \ {0})) =
          ((Set.univ : Set (ZMod 4)) ×ˢ (W : Set ResidualFiber60097)) \ {(0, 0)} ∧
        (W ≠ ⊥ → ∃ x y : ResidualFiber60097, trueTwin60097 W x y)))

end MathlibPlus.Open.Combinatorics
