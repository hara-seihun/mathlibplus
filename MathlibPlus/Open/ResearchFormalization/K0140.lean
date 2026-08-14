import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.K0140

def singleTranspositionCardWitness {V : Type*} [DecidableEq V]
    (deleted : V) (fullVertexPermutation : Equiv.Perm V) : Prop :=
  ∃ u v : V,
    u ≠ v ∧ u ≠ deleted ∧ v ≠ deleted ∧
      fullVertexPermutation = Equiv.swap u v ∧
      fullVertexPermutation deleted = deleted ∧
      ∀ w : V, w ≠ u → w ≠ v → fullVertexPermutation w = w

end MathlibPlus.Open.ResearchFormalization.K0140
