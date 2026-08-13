import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Every valency-fifteen undirected Cayley graph on `C₃² × D₁₀` has the
Cayley-isomorphism property. -/
def c3SquareDihedralTenValencyFifteenUndirectedCI : Prop :=
  let G := (Fin 2 → ZMod 3) × DihedralGroup 5
  ∀ (S T : Set G) (q : G ≃ G),
    1 ∉ S →
    1 ∉ T →
    (∀ x, x ∈ S ↔ x⁻¹ ∈ S) →
    (∀ x, x ∈ T ↔ x⁻¹ ∈ T) →
    Set.ncard S = 15 →
    Set.ncard T = 15 →
    (∀ x y, x⁻¹ * y ∈ S ↔ (q x)⁻¹ * q y ∈ T) →
    ∃ α : G ≃* G, α '' S = T

end MathlibPlus.Open.GraphTheory
