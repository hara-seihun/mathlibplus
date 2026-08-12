import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

namespace MathlibPlus.Open.GraphTheory

/-- Claim 24249: no strongly regular graph has parameters `(405, 132, 63, 33)`. -/
def noSrg_405_132_63_33_claim24249 : Prop :=
  ¬ ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      G.IsSRGWith 405 132 63 33

end MathlibPlus.Open.GraphTheory
