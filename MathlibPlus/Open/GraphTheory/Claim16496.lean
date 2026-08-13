import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

namespace MathlibPlus.Open.GraphTheory

/-- Claim 16496: no strongly regular graph has parameters `(460,153,32,60)`.
The order and strong-regularity conditions are those of Mathlib's exact
`SimpleGraph.IsSRGWith` predicate. -/
def noSrg_460_153_32_60 : Prop :=
  ¬ ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      G.IsSRGWith 460 153 32 60

end MathlibPlus.Open.GraphTheory
