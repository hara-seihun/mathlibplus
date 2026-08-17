import MathlibPlus.Open.Graphs.R0524TreePolynomial

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalization.R0524

noncomputable section

/-- Claim 22343: the connected-set boundary polynomial of a finite tree,
with the outer polynomial variable recording set size and the inner one
recording the components of the deletion complement. -/
def connectedSetBoundaryPolynomial_22343 {V : Type*} [Fintype V]
    [DecidableEq V] (T : SimpleGraph V) (_hT : T.IsTree) :
    Polynomial (Polynomial ℚ) :=
  ∑ S : Finset V,
    if MathlibPlus.Open.Graphs.R0524.connectedSet T S then
      Polynomial.monomial S.card
        (Polynomial.monomial
          (MathlibPlus.Open.Graphs.R0524.complementComponents T S) (1 : ℚ))
    else 0

end

end MathlibPlus.Open.ResearchFormalization.R0524
