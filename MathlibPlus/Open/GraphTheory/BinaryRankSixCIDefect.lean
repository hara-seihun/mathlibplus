import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- There is a valency-28 undirected Cayley-isomorphism defect on the binary
rank-six vector group.  The source connection set contains the seven nonzero
points of an order-eight subgroup, whereas the target contains no such subgroup. -/
def binaryRankSixValencyTwentyEightCIDefect : Prop :=
  let V := Fin 6 → ZMod 2
  ∃ (S T : Set V) (q : V ≃ V),
    q 0 = 0 ∧
    0 ∉ S ∧ 0 ∉ T ∧
    Set.ncard S = 28 ∧ Set.ncard T = 28 ∧
    (∀ x, x ∈ S ↔ -x ∈ S) ∧
    (∀ x, x ∈ T ↔ -x ∈ T) ∧
    (∀ x y, y - x ∈ S ↔ q y - q x ∈ T) ∧
    (∃ W : AddSubgroup V,
      Nat.card W = 8 ∧ ∀ x ∈ W, x ≠ 0 → x ∈ S) ∧
    (∀ W : AddSubgroup V, Nat.card W = 8 →
      ∃ x ∈ W, x ≠ 0 ∧ x ∉ T) ∧
    ¬ ∃ α : V ≃+ V, α '' S = T

end MathlibPlus.Open.GraphTheory
