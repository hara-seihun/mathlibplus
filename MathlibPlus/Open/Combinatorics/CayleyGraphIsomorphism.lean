import Mathlib

namespace MathlibPlus.Open.Combinatorics

/--
Claim 59984: Let `V` be any finite-dimensional vector space over `F₂`, and let
`S,T ⊆ V \ {0}` satisfy `|S|=|T|=7`. If the ordinary simple undirected Cayley
graphs `Cay(V,S)` and `Cay(V,T)` are isomorphic, then there is a linear
automorphism `A ∈ GL(V)` such that `A(S)=T`.
-/
def cayley_graph_isomorphism_linear
    : Prop :=
  ∀ (V : Type*) [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (S T : Set V),
    S ⊆ (Set.univ \ ({0} : Set V)) →
    T ⊆ (Set.univ \ ({0} : Set V)) →
    S.ncard = 7 →
    T.ncard = 7 →
    (SimpleGraph.addCayley S ≃g SimpleGraph.addCayley T) →
    ∃ A : V ≃ₗ[ZMod 2] V, A '' S = T

end MathlibPlus.Open.Combinatorics
