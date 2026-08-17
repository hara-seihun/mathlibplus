import Mathlib

namespace MathlibPlus.Open.Research.CIBinaryTimesC9

abbrev BinaryVector (r : ℕ) := Fin r → ZMod 2
abbrev BinaryTimesC9 (r : ℕ) := BinaryVector r × ZMod 9

private def cycleInflationSet (r : ℕ) (A : Set (BinaryVector r)) : Set (BinaryTimesC9 r) :=
  {g | g.2 = 0 ∧ g.1 ∈ A} ∪
    {g | g.2 = (1 : ZMod 9) ∨ g.2 = -(1 : ZMod 9)}

private def ordinaryCayleyAdjacency
    {G : Type*} [AddGroup G] (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ y - x ∈ S

private def ordinaryCayleyGraphIsomorphism
    {G : Type*} [AddGroup G] (S T : Set G) : Prop :=
  ∃ e : G ≃ G, ∀ x y,
    ordinaryCayleyAdjacency S x y ↔
      ordinaryCayleyAdjacency T (e x) (e y)

private def identityFreeConnectionSet
    {G : Type*} [Zero G] (S : Set G) : Prop :=
  0 ∉ S

private def inverseClosedConnectionSet
    {G : Type*} [Neg G] (S : Set G) : Prop :=
  ∀ x, x ∈ S → -x ∈ S

private def ordinaryUndirectedCIConnectionSet
    {G : Type*} [AddGroup G] (S : Set G) : Prop :=
  identityFreeConnectionSet S ∧
    inverseClosedConnectionSet S ∧
      ∀ T : Set G,
        identityFreeConnectionSet T →
          inverseClosedConnectionSet T →
            ordinaryCayleyGraphIsomorphism S T →
              ∃ α : G ≃+ G, α '' S = T

private def ordinaryCayleyComplement
    {G : Type*} [AddGroup G] (S : Set G) : Set G :=
  ((Set.univ : Set G) \ ({0} : Set G)) \ S

/-- Every displayed cycle inflation and its ordinary Cayley complement is
CI against arbitrary identity-free inverse-closed target connection sets. -/
def claim61042_cycleInflationsAndComplementsAreCI : Prop :=
  ∀ r : ℕ,
    (r = 3 ∨ r = 4 ∨ r = 5) →
      ∀ A : Set (BinaryVector r),
        A ⊆ (Set.univ : Set (BinaryVector r)) \ ({0} : Set (BinaryVector r)) →
          let S_A := cycleInflationSet r A
          ordinaryUndirectedCIConnectionSet S_A ∧
            ordinaryUndirectedCIConnectionSet
              (ordinaryCayleyComplement S_A)

end MathlibPlus.Open.Research.CIBinaryTimesC9
