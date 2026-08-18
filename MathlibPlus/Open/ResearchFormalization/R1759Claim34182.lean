import MathlibPlus.Open.ResearchFormalization.R1759CompleteCarrier
import MathlibPlus.Open.Research.FormalizationBatchUPolynomial

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1759Claim34182

open MathlibPlus.Open.ResearchFormalization.R1759

noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

abbrev EdgeState (V : Type) := Finset (Sym2 V)
abbrev XPoly := MvPolynomial ℕ ℚ
abbrev ZPoly := Polynomial XPoly

/-- The finite states in the complete carrier block `B_Y(C)`. -/
def completeCarrierStates {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) : Finset (EdgeState V) :=
  (record1759EdgeUniverse Y).powerset.filter
    (fun A => A ∈ record1759CompleteCarrierBlock Y C)

/-- The forest on the complement of the carrier, with the selected outside
edges retained in one state. -/
def selectedOutsideGraph {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) (A : EdgeState V) :
    SimpleGraph {v : V // v ∉ C} :=
  SimpleGraph.fromRel (fun u v =>
    Y.Adj u v ∧ s((u : V), (v : V)) ∈ A)

def outsideMonomial {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) (A : EdgeState V) : XPoly :=
  ∏ K : (selectedOutsideGraph Y C A).ConnectedComponent,
    MvPolynomial.X (Set.ncard K.supp)

/-- The unrooted component polynomial of the complement forest `Y-C`. -/
noncomputable def outsideU {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) : XPoly :=
  MvPolynomial.map (Int.castRingHom ℚ)
    (MathlibPlus.Open.ResearchFormalizationBatch.forestUPolynomial
      (SimpleGraph.fromRel (fun u v : {w : V // w ∉ C} => Y.Adj u v)))

/-- The monomial from the selected tree edges inside a connected carrier. -/
def selectedTreeEdgeMonomial {V : Type} (C : Finset V) : ZPoly :=
  Polynomial.X ^ (C.card - 1)

/-- Scalar root-forgetting of one complete carrier state. -/
def rootForgetTerm {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) (A : EdgeState V) : ZPoly :=
  selectedTreeEdgeMonomial C * Polynomial.C (outsideMonomial Y C A)

/-- Scalar contraction of the complete carrier block, retaining every
spectator choice in the complement forest. -/
def scalarizedCompleteCarrierBlock {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) : ZPoly :=
  ∑ A ∈ completeCarrierStates Y C, rootForgetTerm Y C A

/-- Claim 34182: scalar contraction/root-forgetting of the complete carrier
block is the selected internal-tree monomial times the unrooted polynomial of
the complement forest. -/
def claim34182 : Prop :=
  ∀ {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V),
    Y.IsTree → record1759ConnectedCarrier Y C →
      scalarizedCompleteCarrierBlock Y C =
        selectedTreeEdgeMonomial C * Polynomial.C (outsideU Y C)

end

end MathlibPlus.Open.ResearchFormalization.R1759Claim34182
