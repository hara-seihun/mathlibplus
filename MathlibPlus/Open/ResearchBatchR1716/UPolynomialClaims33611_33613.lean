import MathlibPlus.Open.Combinatorics.DTreeUPolynomial

open scoped BigOperators
open MeasureTheory Set Filter Topology

namespace MathlibPlus.Open.ResearchBatchR1716

noncomputable section

open MathlibPlus.Open.Combinatorics.DTreeUPolynomial

/-- The number of connected components represented by a monomial in the
component-size variables. -/
def r1716ComponentDegree (d : ℕ →₀ ℕ) : ℕ :=
  d.support.sum (fun i => d i)

def r1716EulerOperator (p : MvPolynomial ℕ ℤ) : MvPolynomial ℕ ℤ :=
  (MvPolynomial.vars p).sum
    (fun j => MvPolynomial.X j * MvPolynomial.pderiv j p)

/-- Delete one undirected edge while retaining the tree's vertex carrier. -/
def r1716DeleteEdge {V : Type*} (T : SimpleGraph V) (e : V × V) : SimpleGraph V :=
  T \ SimpleGraph.fromEdgeSet {s(e.1, e.2)}

def r1716AggregateDeletedEdgeU {V : Type*} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) : MvPolynomial ℕ ℤ :=
  ∑ e ∈ edgePairs T, uPolynomial (r1716DeleteEdge T e)

/-- The aggregate one-edge-deletion U-polynomial is Euler-minus-one applied
 to the tree U-polynomial. -/
def aggregateEdgeCardIdentity_claim33611 : Prop :=
  ∀ {V : Type*} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V),
    T.IsTree →
      r1716AggregateDeletedEdgeU T =
        r1716EulerOperator (uPolynomial T) - uPolynomial T

/-- For same-order finite trees, equality of U-polynomials is equivalent to
 equality of their aggregate one-edge-deletion U-polynomials. -/
def aggregateEdgeCardEquivalence_claim33613 : Prop :=
  ∀ {V W : Type*} [Fintype V] [Fintype W]
    [LinearOrder V] [LinearOrder W]
    (T : SimpleGraph V) (T' : SimpleGraph W),
    T.IsTree → T'.IsTree →
      Fintype.card V = Fintype.card W →
        (uPolynomial T = uPolynomial T' ↔
          r1716AggregateDeletedEdgeU T =
            r1716AggregateDeletedEdgeU T')

end

end MathlibPlus.Open.ResearchBatchR1716
