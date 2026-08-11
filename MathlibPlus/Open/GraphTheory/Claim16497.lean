import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

namespace MathlibPlus.Open.GraphTheory

/-- Claim 16497: no strongly regular graph has parameters `(85, 14, 3, 2)`.

The source proof is an external finite classification; this registry node
records its exact mathematical conclusion through Mathlib's `IsSRGWith`
predicate, including the vertex-cardinality component. -/
def noSrg_85_14_3_2 : Prop :=
  ¬ ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      G.IsSRGWith 85 14 3 2

