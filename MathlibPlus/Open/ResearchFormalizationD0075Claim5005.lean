import MathlibPlus.Open.UnnormalizedQuantizedRelation

namespace MathlibPlus.Open.ResearchFormalizationD0075

open MathlibPlus.Open.UnnormalizedQuantizedRelation

/-- Claim 5005: the degree-indexed normalized generic lift and deck obey the
Weyl commutator, with the zero-degree convention carried by the operators. -/
def normalizedWeylCommutator_claim5005 : Prop :=
  ∀ n : ℕ,
    FiniteSimpleGraph.deck (n := n) ∘ₗ normalizedLift n -
        (normalizedUpperPrevious n ∘ₗ lower n) =
      LinearMap.id

end MathlibPlus.Open.ResearchFormalizationD0075
