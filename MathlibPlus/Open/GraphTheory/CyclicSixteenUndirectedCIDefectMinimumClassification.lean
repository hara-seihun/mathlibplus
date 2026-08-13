import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Six is the sharp minimum valency of an ordinary undirected Cayley-CI
defect on `C₁₆`; the unique minimum defective graph fibre is represented by
the two displayed connection sets and has an involutive normalized isomorphism. -/
def cyclicSixteenUndirectedCIDefectMinimumClassification : Prop :=
  let G := ZMod 16
  let S₀ : Set G := {2, 3, 5, 11, 13, 14}
  let T₀ : Set G := {3, 5, 6, 10, 11, 13}
  (∀ (S T : Set G) (q : G ≃ G),
      0 ∉ S → 0 ∉ T →
      (∀ x, x ∈ S ↔ -x ∈ S) →
      (∀ x, x ∈ T ↔ -x ∈ T) →
      Set.ncard S < 6 →
      (∀ x y, y - x ∈ S ↔ q y - q x ∈ T) →
      ∃ α : G ≃+ G, α '' S = T) ∧
  AddSubgroup.closure S₀ = ⊤ ∧
  AddSubgroup.closure T₀ = ⊤ ∧
  (∃ q : G ≃ G,
      q 0 = 0 ∧
      (∀ x, q (q x) = x) ∧
      (∀ x y, y - x ∈ S₀ ↔ q y - q x ∈ T₀)) ∧
  (¬ ∃ α : G ≃+ G, α '' S₀ = T₀) ∧
  (∀ (S T : Set G) (q : G ≃ G),
      0 ∉ S → 0 ∉ T →
      (∀ x, x ∈ S ↔ -x ∈ S) →
      (∀ x, x ∈ T ↔ -x ∈ T) →
      Set.ncard S = 6 → Set.ncard T = 6 →
      (∀ x y, y - x ∈ S ↔ q y - q x ∈ T) →
      (¬ ∃ α : G ≃+ G, α '' S = T) →
      ((∃ α β : G ≃+ G, α '' S = S₀ ∧ β '' T = T₀) ∨
       (∃ α β : G ≃+ G, α '' S = T₀ ∧ β '' T = S₀)))

end MathlibPlus.Open.GraphTheory
