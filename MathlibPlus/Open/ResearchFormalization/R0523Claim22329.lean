import MathlibPlus.Open.Research.FormalizationBatchUPolynomial

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0523Claim22329

noncomputable section

abbrev UPolynomial := MvPolynomial ℕ ℤ

/-- The first formal derivative in the singleton-component variable is the
 marked-singleton polynomial of the same finite forest carrier. -/
def claim22329 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V), G.IsAcyclic →
    MathlibPlus.Open.ResearchFormalizationBatch.partialXOne
        (MathlibPlus.Open.ResearchFormalizationBatch.forestUPolynomial G) =
      ∑ v : V,
        MathlibPlus.Open.ResearchFormalizationBatch.forestUPolynomial
          (MathlibPlus.Open.ResearchFormalizationBatch.deletedVertexGraph G v)

end

end MathlibPlus.Open.ResearchFormalization.R0523Claim22329
