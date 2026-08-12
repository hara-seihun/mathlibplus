import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace MathlibPlus.Open.Combinatorics

/--
Claim 58847.  For a finite tree, `c i` counts actual subgraphs with exactly
`i` edges that are connected and contain the prescribed vertex.  The
zero-edge clause is retained as part of the definition-facing statement.
-/
def connectedSubtreeEndpointCountsClaim58847 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj],
    T.IsTree →
      ∀ (n : ℕ), Fintype.card V = n →
        ∀ (w : V),
          let c : ℕ → ℕ := fun i ↦
            Nat.card
              {H : T.Subgraph //
                H.Connected ∧ Nat.card H.coe.edgeSet = i ∧ w ∈ H.verts}
          c 0 = 1

end MathlibPlus.Open.Combinatorics
