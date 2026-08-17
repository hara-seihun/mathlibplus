import MathlibPlus.Open.ResearchBatch.D0014
import MathlibPlus.Open.GraphTheory.Claim4445

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.GraphTheory.Claim4447

/-- The forward constraint multiplicity equals the inverse-edge count on the
same finite simple-edge carrier. -/
def inverseMultiplicityIdentity_claim4447 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (cocycle : MathlibPlus.Open.ResearchBatch.D0014.CardCocycle V)
    (e f : MathlibPlus.Open.ResearchBatch.D0014.SimpleEdge V),
    MathlibPlus.Open.ResearchBatch.D0014.constraintMultiplicity_claim4444
        cocycle e f =
      @Finset.card V
        (@Finset.filter V
          (fun i : V =>
            i ∉ f.1 ∧
              MathlibPlus.Open.GraphTheory.Claim4445.edgeMap
                ((cocycle.pi i).symm) f = e)
          (Classical.decPred _)
          Finset.univ)

end MathlibPlus.Open.GraphTheory.Claim4447
