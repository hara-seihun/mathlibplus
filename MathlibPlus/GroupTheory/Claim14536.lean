import Mathlib

namespace MathlibPlus.GroupTheory.Claim14536

universe u

/-- A finite group is an ordinary undirected CI-group when every isomorphism
of identity-free inverse-closed Cayley connection sets is induced by a group
automorphism. -/
def ordinaryUndirectedCIGroup (G : Type u) [Finite G] [Group G] : Prop :=
  ∀ S T : Set G,
    1 ∉ S →
    (∀ x ∈ S, x⁻¹ ∈ S) →
    1 ∉ T →
    (∀ x ∈ T, x⁻¹ ∈ T) →
    (∃ e : G ≃ G, ∀ x y : G,
      (x⁻¹ * y ∈ S ↔ (e x)⁻¹ * e y ∈ T)) →
    ∃ φ : G ≃* G, Set.image φ S = T

end MathlibPlus.GroupTheory.Claim14536
