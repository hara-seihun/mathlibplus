import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

namespace MathlibPlus.Open.GraphTheory

/-- Claim 16495: no strongly regular graph has parameters `(76, 30, 8, 14)`.

The cited Euclidean and finite-case proof is provenance; the registry node records
its mathematical conclusion using mathlib's `SimpleGraph.IsSRGWith` predicate. -/
def noSrg_76_30_8_14 : Prop :=
  ¬ ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      G.IsSRGWith 76 30 8 14

end MathlibPlus.Open.GraphTheory
