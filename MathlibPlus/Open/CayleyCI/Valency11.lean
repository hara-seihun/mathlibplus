import Mathlib

namespace MathlibPlus.Open.CayleyCI

abbrev G := ZMod 4 × (ZMod 3 × (ZMod 3 × ZMod 3))

def cayleyAdjacent (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ y - x ∈ S

def isCayleyGraphIso (S T : Set G) (f : G → G) : Prop :=
  Function.Bijective f ∧ ∀ x y, cayleyAdjacent S x y ↔ cayleyAdjacent T (f x) (f y)

def cayleyCIValency11 : Prop :=
  ∀ S T : Set G,
    (∀ x, x ∈ S → x ≠ 0) ∧
    (∀ x, x ∈ T → x ≠ 0) ∧
    (∀ x, x ∈ S ↔ -x ∈ S) ∧
    (∀ x, x ∈ T ↔ -x ∈ T) ∧
    min S.ncard (107 - S.ncard) = 11 ∧
    min T.ncard (107 - T.ncard) = 11 →
      ∀ f : G → G, isCayleyGraphIso S T f →
        ∃ α : G ≃+ G, ∀ x, x ∈ S ↔ α x ∈ T

end MathlibPlus.Open.CayleyCI
