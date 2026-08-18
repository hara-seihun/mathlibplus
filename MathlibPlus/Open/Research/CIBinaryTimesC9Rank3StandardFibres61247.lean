import Mathlib

namespace MathlibPlus.Open.Research.CIBinaryTimesC9Rank3StandardFibres61247

/-- The three-dimensional binary factor in the admitted rank-three theorem. -/
abbrev V := Fin 3 → ZMod 2

/-- The direct product `C_2^3 × C_9`. -/
abbrev G := V × ZMod 9

/-- Adjacency in the ordinary undirected Cayley graph on the additive model of
`C_2^3 × C_9`. -/
def cayleyAdjacency (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ y - x ∈ S

/-- A pointed labelled-graph isomorphism between two Cayley presentations. -/
def pointedCayleyGraphIsomorphism
    (S T : Set G) (f : G ≃ G) : Prop :=
  f 0 = 0 ∧
    ∀ x y : G,
      cayleyAdjacency S x y ↔ cayleyAdjacency T (f x) (f y)

/-- Preservation of the standard partition of `G` into the eight fibres of
`G → V`, with no prescribed permutation of the fibres. -/
def preservesStandardC9Fibres (f : G ≃ G) : Prop :=
  ∃ β : V ≃ V,
    ∀ x : V, ∀ z : ZMod 9,
      (f (x, z)).1 = β x

/-- Every pointed graph isomorphism preserving the standard cyclic-nine
fibres is shadowed on its connection set by an additive automorphism of
`C_2^3 × C_9`. -/
def rankThreeStandardC9FibreCI : Prop :=
  ∀ S T : Set G,
    (S ⊆ (Set.univ : Set G) \ ({0} : Set G) ∧
      ∀ x : G, x ∈ S → -x ∈ S) →
    (T ⊆ (Set.univ : Set G) \ ({0} : Set G) ∧
      ∀ x : G, x ∈ T → -x ∈ T) →
    ∀ f : G ≃ G,
      pointedCayleyGraphIsomorphism S T f →
        preservesStandardC9Fibres f →
          ∃ α : G ≃+ G, Set.image (α : G → G) S = T

end MathlibPlus.Open.Research.CIBinaryTimesC9Rank3StandardFibres61247
