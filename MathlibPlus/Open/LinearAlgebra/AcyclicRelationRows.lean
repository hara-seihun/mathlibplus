import Mathlib

namespace MathlibPlus.Open.LinearAlgebra

/-- The bipartite support-incidence graph of a finite relation system. -/
def relationCoordinateGraph {R E : Type*} [DecidableEq E]
    (support : R → Finset E) : SimpleGraph (R ⊕ E) :=
  SimpleGraph.fromRel (fun v w =>
    match v, w with
    | Sum.inl α, Sum.inr e => e ∈ support α
    | _, _ => False)

/-- A finite relation system with nonzero displayed coefficients and forest support incidence. -/
def relationCoordinateIncidenceForest {K R E : Type*} [Zero K]
    [Fintype R] [Fintype E] [DecidableEq E]
    (support : R → Finset E) (coeff : R → E → K) : Prop :=
  (∀ α e, e ∈ support α → coeff α e ≠ 0) ∧
    (∀ α, 2 ≤ (support α).card) ∧
      (relationCoordinateGraph support).IsAcyclic

/-- The coordinate row represented by one relation. -/
def relationRow {K R E : Type*} [Zero K] [DecidableEq E]
    (support : R → Finset E) (coeff : R → E → K) (α : R) : E → K :=
  fun e => if e ∈ support α then coeff α e else 0

/-- The matrix whose rows are the relation vectors. -/
def relationMatrix {K R E : Type*} [Zero K] [DecidableEq E]
    (support : R → Finset E) (coeff : R → E → K) : Matrix R E K :=
  fun α e => relationRow support coeff α e

/-- Forest support incidence and nonzero displayed coefficients force independent rows. -/
def acyclicRelationRowsIndependent {K R E : Type*} [Field K]
    [Fintype R] [Fintype E] [DecidableEq E]
    (support : R → Finset E) (coeff : R → E → K) : Prop :=
  relationCoordinateIncidenceForest support coeff →
    LinearIndependent K (relationRow support coeff) ∧
      Matrix.rank (relationMatrix support coeff) = Fintype.card R

end MathlibPlus.Open.LinearAlgebra
