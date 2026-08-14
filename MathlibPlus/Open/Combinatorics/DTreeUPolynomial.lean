import Mathlib

open scoped Classical BigOperators
noncomputable section

namespace MathlibPlus.Open.Combinatorics.DTreeUPolynomial

section UPolynomial

/-- One oriented representative of each undirected edge. -/
def edgePairs {V : Type*} [Fintype V] [LT V]
    (G : SimpleGraph V) : Finset (V × V) :=
  Finset.univ.filter (fun e => e.1 < e.2 ∧ G.Adj e.1 e.2)

def selectedAdj {V : Type*} [LT V]
    (E : Finset (V × V)) (u v : V) : Prop :=
  (u < v ∧ (u, v) ∈ E) ∨ (v < u ∧ (v, u) ∈ E)

def componentRelation {V : Type*} [LT V]
    (E : Finset (V × V)) : V → V → Prop :=
  Relation.ReflTransGen (selectedAdj E)

def isComponentPartition {V : Type*} [Fintype V] [LT V]
    (E : Finset (V × V)) (P : Finset (Finset V)) : Prop :=
  (∀ C ∈ P, C.Nonempty) ∧
    P.biUnion id = Finset.univ ∧
    (∀ C ∈ P, ∀ D ∈ P, C ≠ D → Disjoint C D) ∧
    (∀ u v, componentRelation E u v →
      ∃ C ∈ P, u ∈ C ∧ v ∈ C) ∧
    (∀ C ∈ P, ∀ u ∈ C, ∀ v ∈ C, componentRelation E u v)

def componentMonomial {V : Type*}
    (P : Finset (Finset V)) : MvPolynomial ℕ ℤ :=
  ∏ C ∈ P, MvPolynomial.X C.card

/-- The standard edge-subset/component-partition U-polynomial on any finite
linearly ordered carrier. -/
def uPolynomial {V : Type*} [Fintype V] [LT V]
    (G : SimpleGraph V) : MvPolynomial ℕ ℤ :=
  ∑ E ∈ (Finset.univ : Finset (Finset (V × V))).filter
      (fun E => E ⊆ edgePairs G),
    ∑ P ∈ (Finset.univ : Finset (Finset (Finset V))).filter
      (fun P => isComponentPartition E P),
      componentMonomial P

end UPolynomial

section Centroid

def centroidVertex {V : Type*} [Fintype V]
    (T : SimpleGraph V) (v : V) : Prop :=
  ∀ C : ((⊤ : T.Subgraph).deleteVerts ({v} : Set V)).coe.ConnectedComponent,
    C.supp.ncard ≤ Fintype.card V / 2

def centroidCore {V : Type*} [Fintype V]
    (T : SimpleGraph V) : Set V :=
  {v | centroidVertex T v}

def unicentroidal {V : Type*} [Fintype V]
    (T : SimpleGraph V) : Prop :=
  ∃! c : V, centroidVertex T c

def bicentroidal {V : Type*} [Fintype V]
    (T : SimpleGraph V) : Prop :=
  ∃ a b : V, a ≠ b ∧ T.Adj a b ∧
    ∀ v : V, centroidVertex T v ↔ v = a ∨ v = b

/-- Claim 6127: the centroid core is exactly the one-vertex or central-edge
centroid set, with both cases represented by one intrinsic predicate. -/
def claim6127 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V),
    T.IsTree →
    ((unicentroidal T →
        ∃ c : V, ∀ v : V, v ∈ centroidCore T ↔ v = c) ∧
      (bicentroidal T →
        ∃ a b : V, a ≠ b ∧ T.Adj a b ∧
          ∀ v : V, v ∈ centroidCore T ↔ v = a ∨ v = b))

/-- Claim 6130: a connected induced majority set contains every centroid. -/
def claim6130 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (C : Set V),
    T.IsTree →
    (T.induce C).Connected →
    C.Nonempty →
    C.ncard > Fintype.card V / 2 →
    ∀ v : V, centroidVertex T v → v ∈ C

end Centroid

section LeafExtensions

def leafExtension {V : Type*}
    (T : SimpleGraph V) (r : V) : SimpleGraph (Option V) :=
  SimpleGraph.fromEdgeSet
    (Sym2.map (fun v : V => some v) '' T.edgeSet ∪
      {s(none, some r)})

def rootOrbit {V : Type*}
    (T : SimpleGraph V) (r r' : V) : Prop :=
  ∃ e : T ≃g T, e.toEquiv r = r'

/-- Claim 6301: one-leaf extensions at different root orbits have different
ordinary U-polynomials. -/
def claim6301 : Prop :=
  ∀ {V : Type*} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (r r' : V),
    T.IsTree →
    ¬ rootOrbit T r r' →
    uPolynomial (leafExtension T r) ≠
      uPolynomial (leafExtension T r')

end LeafExtensions

section EdgeCards

/-- Claim 6336: differentiating in the size-two variable is the sum over all
edge cards, with the deleted vertices carried by the induced subtype. -/
def claim6336 : Prop :=
  ∀ {V : Type*} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V),
    T.IsTree →
    MvPolynomial.pderiv 2 (uPolynomial T) =
      ∑ e ∈ edgePairs T,
        uPolynomial (T.induce {x : V | x ≠ e.1 ∧ x ≠ e.2})

def fixtureGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet
    {s(0, 1), s(0, 2), s(1, 3)}

def subhalfProjection (p : MvPolynomial ℕ ℤ) : MvPolynomial ℕ ℤ :=
  ∑ d ∈ p.support,
    if ∀ i ∈ d.support, i < 2 then
      MvPolynomial.monomial d (p.coeff d)
    else 0

/-- Claim 6338: the explicit four-vertex fixture has the displayed central and
noncentral edge-card U-polynomials and scalar derivative leakage. -/
def claim6338 : Prop :=
  let x₁ : MvPolynomial ℕ ℤ := MvPolynomial.X 1
  let x₂ : MvPolynomial ℕ ℤ := MvPolynomial.X 2
  let T := fixtureGraph
  (uPolynomial (T.induce {x : Fin 4 | x ≠ 0 ∧ x ≠ 1}) = x₁ ^ 2) ∧
  (uPolynomial (T.induce {x : Fin 4 | x ≠ 0 ∧ x ≠ 2}) = x₂ + x₁ ^ 2) ∧
  (uPolynomial (T.induce {x : Fin 4 | x ≠ 1 ∧ x ≠ 3}) = x₂ + x₁ ^ 2) ∧
  MvPolynomial.pderiv 2 (uPolynomial T) = 3 * x₁ ^ 2 + 2 * x₂

/-- Claim 6339: deleting all variables of size at least two does not isolate
this fixture's central edge card. -/
def claim6339 : Prop :=
  let x₁ : MvPolynomial ℕ ℤ := MvPolynomial.X 1
  let x₂ : MvPolynomial ℕ ℤ := MvPolynomial.X 2
  subhalfProjection (MvPolynomial.pderiv 2 (uPolynomial fixtureGraph)) =
      3 * x₁ ^ 2 ∧
    3 * x₁ ^ 2 ≠ x₁ ^ 2

end EdgeCards

end MathlibPlus.Open.Combinatorics.DTreeUPolynomial
