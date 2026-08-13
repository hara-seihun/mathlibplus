import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Every ordinary undirected Cayley graph on the binary rank-six vector group
with valency at most eighteen has the Cayley-isomorphism property. -/
def binaryRankSixValencyAtMostEighteenCI : Prop :=
  let V := Fin 6 → ZMod 2
  ∀ (S T : Set V) (q : V ≃ V),
    0 ∉ S →
    0 ∉ T →
    (∀ x, x ∈ S ↔ -x ∈ S) →
    (∀ x, x ∈ T ↔ -x ∈ T) →
    Set.ncard S ≤ 18 →
    (∀ x y, y - x ∈ S ↔ q y - q x ∈ T) →
    ∃ α : V ≃+ V, α '' S = T

end MathlibPlus.Open.GraphTheory
