import MathlibPlus.Open.ResearchFormalization.R0523Claim22326

namespace MathlibPlus.Open.ResearchFormalization.R0523Claim22323

noncomputable section

open Classical
open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization.R0523Claim22338
open MathlibPlus.Open.ResearchFormalizationBatch

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev UPolynomial := MvPolynomial ℕ ℤ

/-- The ordinary component polynomial on the reviewed U-polynomial carrier. -/
def ordinaryForestComponentPolynomial {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) : UPolynomial :=
  MvPolynomial.map (Nat.castRingHom ℤ) (graphUPolynomial G)

/-- The explicit edge-subset/component expansion of the ordinary component
polynomial, using the selected spanning graph on all vertices. -/
def ordinaryForestComponentExpansion {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) : UPolynomial :=
  ∑ A ∈ (Finset.univ : Finset (↥G.edgeSet)).powerset,
    MvPolynomial.map (Nat.castRingHom ℤ)
      (spanningComponentMonomial G A)

/-- Claim 22323: every finite forest has the displayed ordinary component
polynomial, and the empty forest has the empty-product value one. -/
def claim22323_ordinaryForestComponentPolynomial : Prop :=
  (∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V),
      G.IsAcyclic →
        ordinaryForestComponentPolynomial G =
          ordinaryForestComponentExpansion G) ∧
    ordinaryForestComponentPolynomial (⊥ : SimpleGraph (Fin 0)) = 1

end

end MathlibPlus.Open.ResearchFormalization.R0523Claim22323
