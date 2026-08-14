import Mathlib

open BigOperators

namespace MathlibPlus.Open.Combinatorics.MotifStoppingSet

noncomputable section

open Classical

/-- A target set whose adjacent cards have a nonzero dependence supported on
occurrences landing in the target set. The arguments are the card nodes,
occurrence nodes, target nodes, feature coordinates, and feature labels of the
leaf-extension Tanner data. -/
def motifStoppingSet {C V T F R : Type*} [Semiring R]
    (occurrences : C → Finset V) (attach : C → V → T)
    (feature : C → F → V → R) (S : Set T) : Prop :=
  ∀ c, (∃ v ∈ occurrences c, attach c v ∈ S) →
    ∃ coeff : V → R,
      (∀ v, v ∉ occurrences c → coeff v = 0) ∧
      (∀ v, v ∈ occurrences c → attach c v ∉ S → coeff v = 0) ∧
      (∃ v ∈ occurrences c, attach c v ∈ S ∧ coeff v ≠ 0) ∧
      (∀ f, ∑ v ∈ occurrences c, feature c f v * coeff v = 0)

end
end MathlibPlus.Open.Combinatorics.MotifStoppingSet
