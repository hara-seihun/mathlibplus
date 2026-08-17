import MathlibPlus.Open.Combinatorics.Claim5539Formalization

namespace MathlibPlus.Open.Combinatorics.Claim5538

open MathlibPlus.Open.Combinatorics.Claim5539Formalization

/-- The dependency digraph of an incident-row selector has exactly the
support-minus-the-selected-column arrows from the admitted statement.  The
selector is supplied together with its incident-row proof, so no arbitrary
relation callback is introduced. -/
def incidentRowSelectorDependencyDigraph_claim5538
    {K R C : Type*} [Field K] [Fintype R] [Fintype C]
    (A : Matrix R C K) (s : C → R)
    (_hs : incidentRowSelector A s) : C → C → Prop :=
  fun c d => d ∈ rowSupport A (s c) \ {c}

end MathlibPlus.Open.Combinatorics.Claim5538
