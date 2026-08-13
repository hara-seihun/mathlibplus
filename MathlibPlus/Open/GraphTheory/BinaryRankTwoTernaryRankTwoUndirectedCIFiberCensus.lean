import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The ordinary undirected Cayley presentations on `C₂² × C₃²` have exactly
6170 additive-automorphism orbits, and every unlabelled graph-isomorphism fiber
is a singleton on those orbits. -/
def binaryRankTwoTernaryRankTwoUndirectedCIFiberCensus : Prop :=
  let G := (Fin 2 → ZMod 2) × (Fin 2 → ZMod 3)
  let Admissible := fun S : Set G =>
    (0 : G) ∉ S ∧ ∀ x, x ∈ S ↔ -x ∈ S
  ∃ code : Set G → Fin 6170,
    (∀ (S T : Set G), Admissible S → Admissible T →
      (code S = code T ↔ ∃ α : G ≃+ G, α '' S = T)) ∧
    (∀ i : Fin 6170, ∃ S : Set G, Admissible S ∧ code S = i) ∧
    (∀ (S T : Set G), Admissible S → Admissible T →
      ((∃ e : G ≃ G,
        ∀ x y : G, y - x ∈ S ↔ e y - e x ∈ T) ↔
        code S = code T))

end MathlibPlus.Open.GraphTheory
