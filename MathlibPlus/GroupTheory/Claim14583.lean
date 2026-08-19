import MathlibPlus.GraphTheory.CayleyCIHierarchy

namespace MathlibPlus.GroupTheory.Claim14583

open MathlibPlus.GraphTheory

/-- Claim 14583: the ordinary undirected CI predicate is attached to one
fixed finite group and uses inverse-closed `SimpleGraph.mulCayley` objects. -/
def ordinaryUndirectedCIProperty_claim14583
    (G : Type*) [Finite G] [Group G] : Prop :=
  IsCayleyGraphCI G

end MathlibPlus.GroupTheory.Claim14583
