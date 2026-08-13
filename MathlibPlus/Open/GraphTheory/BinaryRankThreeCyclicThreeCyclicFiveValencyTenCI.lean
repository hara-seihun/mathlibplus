import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The first canon-open finite A5 group `C₂³ × C₃ × C₅` is ordinary
Cayley-CI through valency ten. -/
def binaryRankThreeCyclicThreeCyclicFiveValencyAtMostTenCI : Prop :=
  let G := (Fin 3 → ZMod 2) × ZMod 3 × ZMod 5
  ∀ S T : Set G,
    0 ∉ S →
    0 ∉ T →
    (∀ x, x ∈ S ↔ -x ∈ S) →
    (∀ x, x ∈ T ↔ -x ∈ T) →
    S.ncard ≤ 10 →
    (∃ q : G ≃ G, ∀ x y : G,
      y - x ∈ S ↔ q y - q x ∈ T) →
    ∃ α : G ≃+ G, α '' S = T

end MathlibPlus.Open.GraphTheory
