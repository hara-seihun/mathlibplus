import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Every profile of origin transpositions on the cyclic-nine fibres of
`C₂³ × C₉` fixes every compatible ordinary undirected connection set. -/
def binaryRankThreeCyclicNineDualOriginTranspositionProfilesFixConnectionSets : Prop :=
  let V := Fin 3 → ZMod 2
  let G := V × ZMod 9
  ∀ u : V → ZMod 9, u 0 = 0 →
    let q : G → G := fun x =>
      (x.1, Equiv.swap (0 : ZMod 9) (u x.1) x.2)
    ∀ S T : Set G,
      (0 : G) ∉ S →
      (0 : G) ∉ T →
      (∀ x ∈ S, -x ∈ S) →
      (∀ x ∈ T, -x ∈ T) →
      (∀ x y : G, y - x ∈ S ↔ q y - q x ∈ T) →
      q '' S = S ∧ T = S

end MathlibPlus.Open.GraphTheory
