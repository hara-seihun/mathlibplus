import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Every ordinary undirected Cayley graph of valency eleven on the elementary
abelian group `F₂⁶` has the CI property. -/
def binaryRankSixValencyElevenCI : Prop :=
  let V := Fin 6 → ZMod 2
  ∀ (S T : Set V),
    0 ∉ S →
    0 ∉ T →
    (∀ x, x ∈ S ↔ -x ∈ S) →
    (∀ x, x ∈ T ↔ -x ∈ T) →
    S.ncard = 11 →
    T.ncard = 11 →
    (∃ q : V ≃ V, ∀ x y : V,
      y - x ∈ S ↔ q y - q x ∈ T) →
    ∃ α : V ≃+ V, α '' S = T

end MathlibPlus.Open.GraphTheory
