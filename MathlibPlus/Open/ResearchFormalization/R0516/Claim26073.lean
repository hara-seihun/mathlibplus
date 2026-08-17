import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0516

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable

abbrev ColorVar (q : ℕ) := Sum (Fin q) (Sum (Fin q) Unit)
abbrev ComplementVertex {V : Type*} (S : Finset V) := {v : V // v ∉ S}

/-- The two vertex-color variables and two monochromatic-edge variables for a
q-color generalized-degree polynomial. -/
def xVar (q : ℕ) (i : Fin q) : ColorVar q := Sum.inl i
def zVar (q : ℕ) (i : Fin q) : ColorVar q := Sum.inr (Sum.inl i)
def yVar (q : ℕ) : ColorVar q := Sum.inr (Sum.inr ())

/-- Whether all endpoints of an edge have the displayed color. -/
def edgeHasColor {V : Type*} {q : ℕ}
    (c : V → Fin q) {G : SimpleGraph V} [Fintype V]
    [DecidableRel G.Adj] (e : G.edgeSet) (i : Fin q) : Prop :=
  ∀ v, v ∈ e.1 → c v = i

/-- An edge is monochromatic for the coloring. -/
def edgeMonochromatic {V : Type*} {q : ℕ}
    (c : V → Fin q) {G : SimpleGraph V} [Fintype V]
    [DecidableRel G.Adj] (e : G.edgeSet) : Prop :=
  ∃ i, edgeHasColor c e i

/-- The literal generalized-degree edge weight: a monochromatic edge records
its color by z_i, while an unequal-color edge records y. -/
def edgeWeight {V : Type*} (q : ℕ)
    (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (c : V → Fin q) (e : G.edgeSet) : MvPolynomial (ColorVar q) ℤ :=
  if edgeMonochromatic c e then
    ∑ i : Fin q,
      if edgeHasColor c e i then MvPolynomial.X (zVar q i) else 0
  else MvPolynomial.X (yVar q)

/-- The monomial for one q-coloring, with vertex and edge statistics literal. -/
noncomputable def gDegreeMonomial {V : Type*} (q : ℕ)
    (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (c : V → Fin q) : MvPolynomial (ColorVar q) ℤ :=
  (∏ v : V, MvPolynomial.X (xVar q (c v))) *
    (∏ e : G.edgeSet, edgeWeight q G c e)

/-- The finite-color generalized-degree polynomial. -/
noncomputable def gDegreePolynomial {V : Type*} (q : ℕ)
    (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] :
    MvPolynomial (ColorVar q) ℤ :=
  ∑ c : V → Fin q, gDegreeMonomial q G c

/-- The literal one-color Liu--Tang polynomial `G^(1)`. -/
noncomputable def GOne {V : Type*}
    (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] :
    MvPolynomial (ColorVar 2) ℤ :=
  gDegreePolynomial 2 G

/-- The finite graph induced on the complement of a fixed support. -/
def inducedComplement {V : Type*} (G : SimpleGraph V)
    (S : Finset V) : SimpleGraph (ComplementVertex S) :=
  G.induce {v | v ∉ S}

/-- A binary residual color is embedded into the two non-marked ternary
colors, 0 and 2. -/
def liftBinaryColor (i : Fin 2) : Fin 3 :=
  if i = 0 then 0 else 2

/-- Extend a residual binary coloring by assigning marked color 1 on S. -/
def extendResidualColoring {V : Type*} (S : Finset V)
    (r : ComplementVertex S → Fin 2) : V → Fin 3 :=
  fun v =>
    if h : v ∈ S then 1 else liftBinaryColor (r ⟨v, h⟩)

/-- The total residual color used on a host vertex, for describing edges wholly
outside the fixed support. -/
def residualColorAt {V : Type*} (S : Finset V)
    (r : ComplementVertex S → Fin 2) (v : V) : Fin 2 :=
  if h : v ∉ S then r ⟨v, h⟩ else 0

/-- A host edge meets both S and its complement. -/
def boundaryEdge {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj]
    (S : Finset V) (e : G.edgeSet) : Prop :=
  (∃ u, u ∈ e.1 ∧ u ∈ S) ∧ ∃ v, v ∈ e.1 ∧ v ∉ S

/-- A host edge lies wholly inside one side of the fixed support. -/
def internalEdge {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj]
    (S : Finset V) (e : G.edgeSet) : Prop :=
  ∀ v, v ∈ e.1 → v ∈ S

def outsideEdge {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj]
    (S : Finset V) (e : G.edgeSet) : Prop :=
  ∀ v, v ∈ e.1 → v ∉ S

/-- The boundary-edge count `d_T(S)`. -/
def boundaryCount {V : Type*} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  ((Finset.univ : Finset G.edgeSet).filter (boundaryEdge S)).card

/-- Unequal-color host edges for one coloring. -/
def unequalEdgeSet {V : Type*} {q : ℕ}
    (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (c : V → Fin q) : Finset G.edgeSet :=
  (Finset.univ : Finset G.edgeSet).filter (fun e => ¬ edgeMonochromatic c e)

/-- Boundary edges and wholly-outside unequal edges, represented on the host
edge carrier so their disjoint union is literal. -/
def boundaryEdgeSet {V : Type*} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] (S : Finset V) : Finset G.edgeSet :=
  (Finset.univ : Finset G.edgeSet).filter (boundaryEdge S)

def residualUnequalEdgeSet {V : Type*} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] (S : Finset V)
    (r : ComplementVertex S → Fin 2) : Finset G.edgeSet :=
  (Finset.univ : Finset G.edgeSet).filter (fun e =>
    outsideEdge S e ∧
      ¬ edgeMonochromatic (residualColorAt S r) e)

/-- The fixed-support coefficient contribution, independently defined by
summing the residual colorings and retaining boundary y-weights. -/
noncomputable def fixedSupportCoefficientContribution {V : Type*}
    (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (S : Finset V) : MvPolynomial (ColorVar 2) ℤ :=
  ∑ r : ComplementVertex S → Fin 2,
    (∏ v : ComplementVertex S,
      MvPolynomial.X (xVar 2 (r v))) *
      (∏ e : G.edgeSet,
        if boundaryEdge S e then MvPolynomial.X (yVar 2)
        else if outsideEdge S e then edgeWeight 2 G (residualColorAt S r) e
        else 1)

/-- Claim 26073: at a fixed support, unequal edges split disjointly into the
support boundary and the unequal edges of the deleted complement; after the
residual colorings are summed, the fixed-support contribution is the boundary
`y`-weight times the literal `G^(1)` of the complement. -/
def unequalEdgeStatisticFixedSupport_claim26073 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj]
    (S : Finset V),
    (∀ r : ComplementVertex S → Fin 2,
      Disjoint (boundaryEdgeSet T S) (residualUnequalEdgeSet T S r) ∧
      unequalEdgeSet T (extendResidualColoring S r) =
        boundaryEdgeSet T S ∪ residualUnequalEdgeSet T S r ∧
      (unequalEdgeSet T (extendResidualColoring S r)).card =
        (boundaryEdgeSet T S).card +
          (residualUnequalEdgeSet T S r).card) ∧
    fixedSupportCoefficientContribution T S =
      (MvPolynomial.X (yVar 2) : MvPolynomial (ColorVar 2) ℤ) ^
          boundaryCount T S * GOne (inducedComplement T S)

end

end MathlibPlus.Open.ResearchFormalization.R0516
