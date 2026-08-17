import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0330Claim19947

noncomputable section
open Classical
open scoped BigOperators

/-- The variables of an m-layer deck: x-variables, z-variables, and the
common cut variable y. -/
abbrev DeckVar (m : ℕ) := Fin m ⊕ (Fin m ⊕ Unit)

def xVar (m : ℕ) (i : Fin m) : DeckVar m :=
  Sum.inl i

def zVar (m : ℕ) (i : Fin m) : DeckVar m :=
  Sum.inr (Sum.inl i)

def yVar (m : ℕ) : DeckVar m :=
  Sum.inr (Sum.inr ())

def shiftVar {m : ℕ} : DeckVar m → DeckVar (m + 1)
  | Sum.inl i => Sum.inl i.succ
  | Sum.inr (Sum.inl i) => Sum.inr (Sum.inl i.succ)
  | Sum.inr (Sum.inr u) => Sum.inr (Sum.inr u)

/-- The fixed-vertex edge carrier and its simple-graph carrier. -/
def Edge (V : Type) := {s : Finset V // s.card = 2}
abbrev Graph (V : Type) := Finset (Edge V)

/-- The finite edge set of a simple graph, using the exact endpoint carrier
of `SimpleGraph`. -/
def graphEdges {V : Type} [Fintype V] (F : SimpleGraph V) :
    Finset (Sym2 V) :=
  Finset.univ.filter (fun e : Sym2 V => e ∈ F.edgeSet)

def edgeWithin {V : Type} (A : Finset V) (e : Sym2 V) : Prop :=
  ∀ v : V, Sym2.Mem v e → v ∈ A

def edgeCrosses {V : Type} (A : Finset V) (e : Sym2 V) : Prop :=
  ∃ u v : V, u ∈ A ∧ v ∉ A ∧ Sym2.Mem u e ∧ Sym2.Mem v e

def internalEdgeCount {V : Type} [Fintype V]
    (F : SimpleGraph V) (A : Finset V) : ℕ :=
  (graphEdges F).filter (edgeWithin A) |>.card

def crossingEdgeCount {V : Type} [Fintype V]
    (F : SimpleGraph V) (A : Finset V) : ℕ :=
  (graphEdges F).filter (edgeCrosses A) |>.card

def deletedGraph {V : Type} (F : SimpleGraph V) (A : Finset V) :
    SimpleGraph {v : V // v ∉ A} :=
  F.induce {v : V | v ∉ A}

abbrev DeckPolynomial (V : Type) [Fintype V] (m : ℕ) :=
  MvPolynomial (DeckVar m) ℤ

/-- The iterated induced-subgraph deck transform, with its exact x/z/cut
variables. -/
def deckInvariant {V : Type} [Fintype V] (F : SimpleGraph V) :
    (m : ℕ) → DeckPolynomial V m
  | 0 => 1
  | m + 1 =>
      ∑ A : Finset V,
        (MvPolynomial.X (xVar (m + 1) 0) ^ A.card) *
          (MvPolynomial.X (zVar (m + 1) 0) ^ internalEdgeCount F A) *
          (MvPolynomial.X (yVar (m + 1)) ^ crossingEdgeCount F A) *
          MvPolynomial.rename (shiftVar : DeckVar m → DeckVar (m + 1))
            (deckInvariant (deletedGraph F A) m)

/-- Coefficient extraction in one named variable, retaining the remaining
variables as a polynomial in the same ambient variable type. -/
def variableCoefficient {σ : Type} [DecidableEq σ]
    (p : MvPolynomial σ ℤ) (v : σ) (a : ℕ) : MvPolynomial σ ℤ :=
  (p.support.filter (fun d => d v = a)).sum
    (fun d => MvPolynomial.monomial (Finsupp.erase v d)
      (MvPolynomial.coeff d p))

def xOneCoefficient {V : Type} [Fintype V] (m : ℕ)
    (p : DeckPolynomial V (m + 1)) (a : ℕ) : DeckPolynomial V (m + 1) :=
  variableCoefficient p (xVar (m + 1) 0) a

def zOneCoefficient {V : Type} [Fintype V] (m : ℕ)
    (p : DeckPolynomial V (m + 1)) (a : ℕ) : DeckPolynomial V (m + 1) :=
  variableCoefficient p (zVar (m + 1) 0) a

def inducedLayer {V : Type} [Fintype V] (F : SimpleGraph V)
    (m a : ℕ) : DeckPolynomial V (m + 1) :=
  ∑ A : Finset V,
    if A.card = a then
      (MvPolynomial.X (zVar (m + 1) 0) ^ internalEdgeCount F A) *
        (MvPolynomial.X (yVar (m + 1)) ^ crossingEdgeCount F A) *
        MvPolynomial.rename (shiftVar : DeckVar m → DeckVar (m + 1))
          (deckInvariant (deletedGraph F A) m)
    else 0

def edgeDeckLayer {V : Type} [Fintype V] (F : SimpleGraph V)
    (m : ℕ) : DeckPolynomial V (m + 1) :=
  ∑ A : Finset V,
    if A.card = 2 ∧ internalEdgeCount F A = 1 then
      (MvPolynomial.X (yVar (m + 1)) ^ crossingEdgeCount F A) *
        MvPolynomial.rename (shiftVar : DeckVar m → DeckVar (m + 1))
          (deckInvariant (deletedGraph F A) m)
    else 0

/-- Claim 19947: every x₁ coefficient is the exact induced-subgraph deletion
layer, and the x₁²z₁ specialization is the edge-deck layer. -/
def claim19947 : Prop :=
  ∀ {V : Type} [Fintype V] (F : SimpleGraph V), SimpleGraph.IsAcyclic F →
    ∀ (m a : ℕ),
      xOneCoefficient m (deckInvariant F (m + 1)) a =
        inducedLayer F m a ∧
      zOneCoefficient m
          (xOneCoefficient m (deckInvariant F (m + 1)) 2) 1 =
        edgeDeckLayer F m

end
end MathlibPlus.Open.ResearchFormalization.R0330Claim19947
