import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchR1258R1260R1551

/-- The identity-free ordinary undirected Cayley adjacency relation. -/
def cayleyAdjacent {G : Type*} [Group G]
    (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ x⁻¹ * y ∈ S

/-- The ordinary undirected CI property: every graph isomorphism between
identity-free inverse-closed Cayley graphs is induced on the connection set by
an automorphism of the group. -/
def ordinaryUndirectedCIGroup {G : Type*} [Group G] [Fintype G] : Prop :=
  ∀ S T : Set G,
    (1 : G) ∉ S →
      (∀ x, x ∈ S → x⁻¹ ∈ S) →
        (1 : G) ∉ T →
          (∀ x, x ∈ T → x⁻¹ ∈ T) →
            (∃ e : G ≃ G, ∀ x y,
              cayleyAdjacent S x y ↔ cayleyAdjacent T (e x) (e y)) →
              ∃ α : G ≃* G, α '' S = T

/-- Claim 31111: the repaired ordinary-CI conclusion for the finite
 generalized-quaternion group `Q₁₅₆ = QuaternionGroup 39` (the case `p=13`). -/
def claim31111 : Prop :=
  Fintype.card (QuaternionGroup 39) = 156 ∧
    ordinaryUndirectedCIGroup (G := QuaternionGroup 39)

end MathlibPlus.Open.ResearchFormalization.BatchR1258R1260R1551
