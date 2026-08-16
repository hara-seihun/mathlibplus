import Mathlib

namespace MathlibPlus.Open.CayleyCI

abbrev F3 := ZMod 3
abbrev V := Fin 3 → F3
abbrev G := ZMod 4 × V

def cayleyAdjacency (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ x - y ∈ S

def cayleyGraphIso (S T : Set G) : Prop :=
  ∃ f : G → G,
    Function.Bijective f ∧
      ∀ x y : G,
        cayleyAdjacency S x y ↔ cayleyAdjacency T (f x) (f y)

def nongeneratingA5 : Prop :=
  ∀ (S T : Set G),
    S ⊆ Set.univ \ ({0} : Set G) →
    T ⊆ Set.univ \ ({0} : Set G) →
    (∀ x ∈ S, -x ∈ S) →
    (∀ x ∈ T, -x ∈ T) →
    AddSubgroup.closure S ≠ ⊤ →
    cayleyGraphIso S T →
    ∃ α : G ≃+ G, α '' S = T

end MathlibPlus.Open.CayleyCI
