import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- Ordinary undirected Cayley adjacency for an inverse-closed connection set. -/
def c3CayleyAdjacency (S : Set (ZMod 3)) (a b : ZMod 3) : Prop :=
  a ≠ b ∧ b - a ∈ S

/-- Claim 59899: C₃ is a CI-group for ordinary undirected Cayley graphs. -/
def c3IsCIGroupOrdinaryUndirected : Prop :=
  ∀ S T : Set (ZMod 3),
    (0 ∉ S ∧ (∀ s, s ∈ S → -s ∈ S)) ∧
      (0 ∉ T ∧ (∀ t, t ∈ T → -t ∈ T)) →
        (∃ e : ZMod 3 ≃ ZMod 3,
          ∀ a b,
            c3CayleyAdjacency S a b ↔
              c3CayleyAdjacency T (e a) (e b)) →
          S = T ∧ Set.image (AddEquiv.refl (ZMod 3)) S = T

end MathlibPlus.Open.ResearchFormalization
