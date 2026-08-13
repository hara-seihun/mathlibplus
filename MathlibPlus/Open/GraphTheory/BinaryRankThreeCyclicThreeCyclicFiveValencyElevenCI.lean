import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Every ordinary undirected Cayley graph of valency eleven on
`C₂³ × C₃ × C₅` has the CI property. -/
def binaryRankThreeCyclicThreeCyclicFiveValencyElevenCI : Prop :=
  let G := (Fin 3 → ZMod 2) × ZMod 3 × ZMod 5
  ∀ S T : Set G,
    0 ∉ S →
    0 ∉ T →
    (∀ x, x ∈ S ↔ -x ∈ S) →
    (∀ x, x ∈ T ↔ -x ∈ T) →
    S.ncard = 11 →
    T.ncard = 11 →
    (∃ q : G ≃ G, ∀ x y : G,
      y - x ∈ S ↔ q y - q x ∈ T) →
    ∃ α : G ≃+ G, α '' S = T

end MathlibPlus.Open.GraphTheory
