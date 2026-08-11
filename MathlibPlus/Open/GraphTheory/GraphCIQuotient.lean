import Mathlib

namespace MathlibPlus.Open.GraphTheory

/--
Claim 28338: the undirected graph-CI property is inherited by finite normal
quotients.  Inverse-closed, identity-free connection sets and graph
isomorphisms are written out at both group levels.
-/
def graphCIHereditaryToNormalQuotients : Prop :=
  ∀ (G : Type*) [Finite G] [Group G] (N : Subgroup G) [N.Normal],
    (∀ (S T : Set G), S = S⁻¹ → T = T⁻¹ → 1 ∉ S → 1 ∉ T →
      Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) →
        ∃ φ : G ≃* G, φ '' S = T) →
    (∀ (S T : Set (G ⧸ N)), S = S⁻¹ → T = T⁻¹ → 1 ∉ S → 1 ∉ T →
      Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) →
        ∃ φ : (G ⧸ N) ≃* (G ⧸ N), φ '' S = T)

end MathlibPlus.Open.GraphTheory
