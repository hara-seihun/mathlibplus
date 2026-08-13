import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Every valency-fourteen undirected Cayley graph on `C₃² × D₁₀` has the
Cayley-isomorphism property. -/
def c3SquareDihedralTenValencyFourteenUndirectedCI : Prop :=
  let G := (Fin 2 → ZMod 3) × DihedralGroup 5
  ∀ (S T : Set G) (q : G ≃ G),
    1 ∉ S →
    1 ∉ T →
    (∀ x, x ∈ S ↔ x⁻¹ ∈ S) →
    (∀ x, x ∈ T ↔ x⁻¹ ∈ T) →
    Set.ncard S = 14 →
    Set.ncard T = 14 →
    (∀ x y, x⁻¹ * y ∈ S ↔ (q x)⁻¹ * q y ∈ T) →
    ∃ α : G ≃* G, α '' S = T

end MathlibPlus.Open.GraphTheory
