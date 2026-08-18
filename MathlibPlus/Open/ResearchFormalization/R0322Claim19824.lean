import MathlibPlus.Open.ResearchFormalization.R0322DoubleSpiderClaims

namespace MathlibPlus.Open.ResearchFormalization.R0322Claim19824

open scoped BigOperators Classical
open MathlibPlus.Open.ResearchFormalization.R0322DoubleSpiderClaims

noncomputable section

/-- The singleton-refined signed cut polynomial supplied by the reviewed
component-weight construction: singleton components carry `Y`, while every
component of order at least two carries `1 + X * Q^(s - 1)`. -/
def singletonRefinedCutPolynomial {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) : ScalarPoly :=
  cutPolynomial F

/-- The singleton-refined forest polynomial is multiplicative on disjoint
unions of forests. -/
def singletonRefinedForestPolynomial_claim19824 : Prop :=
  ∀ {V W : Type} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) (G : SimpleGraph W),
    F.IsAcyclic → G.IsAcyclic →
      singletonRefinedCutPolynomial (SimpleGraph.sum F G) =
        singletonRefinedCutPolynomial F * singletonRefinedCutPolynomial G

end

end MathlibPlus.Open.ResearchFormalization.R0322Claim19824
