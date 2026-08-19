import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R3893Claim51680

noncomputable section

open scoped BigOperators Classical

/-- A rooted tree of order `n`, presented on the canonical carrier `Fin n`. -/
abbrev RootedTree (n : ℕ) :=
  {G : SimpleGraph (Fin n) // G.IsTree} × Fin n

/-- A signed same-order packet is an integer-valued finitely supported family
of rooted trees with one common order. -/
abbrev SignedRootedPacket (n : ℕ) := RootedTree n →₀ ℤ

/-- The graph consisting of exactly the selected edges. -/
def selectedEdgeGraph {n : ℕ}
    (A : Finset (Sym2 (Fin n))) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v => s(u, v) ∈ A)

/-- The component of a vertex in a selected-edge graph. -/
def componentSet {V : Type*}
    (G : SimpleGraph V) (v : V) : Set V :=
  {w | G.Reachable v w}

/-- The finite family of all connected components. -/
def componentFamily {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Finset (Set V) :=
  Finset.univ.image (componentSet G)

/-- The selected component containing the distinguished root. -/
def rootComponent {n : ℕ}
    (R : RootedTree n) (A : Finset (Sym2 (Fin n))) : Set (Fin n) :=
  componentSet (selectedEdgeGraph A) R.2

/-- The order of the root component and the multiset of all other component
orders. -/
def rootComponentOrder {n : ℕ}
    (R : RootedTree n) (A : Finset (Sym2 (Fin n))) : ℕ :=
  (rootComponent R A).ncard

def nonrootComponentOrders {n : ℕ}
    (R : RootedTree n) (A : Finset (Sym2 (Fin n))) : Multiset ℕ :=
  ((componentFamily (selectedEdgeGraph A)).filter
      (fun C => C ≠ rootComponent R A)).1.map
    (fun C => C.ncard)

/-- The product of the component-size variables `x_(lambda_i)`, with the
multiplicity prescribed from the multiset `lambda`. -/
def componentOrderMonomial (lambda : Multiset ℕ) : MvPolynomial ℕ ℚ :=
  (lambda.map (fun s => MvPolynomial.X s)).prod

/-- The exact open-root monomial `z^a x_lambda`. -/
def openRootMonomial {n : ℕ}
    (R : RootedTree n) (A : Finset (Sym2 (Fin n))) :
    MvPolynomial (Option ℕ) ℚ :=
  (MvPolynomial.X (none : Option ℕ) :
      MvPolynomial (Option ℕ) ℚ) ^ rootComponentOrder R A *
    ((nonrootComponentOrders R A).map
      (fun s => MvPolynomial.X (some s))).prod

/-- The complete open-root spanning-forest polynomial `J_R`. -/
def openRootForestPolynomial {n : ℕ}
    (R : RootedTree n) : MvPolynomial (Option ℕ) ℚ :=
  ∑ A ∈ R.1.1.edgeFinset.powerset, openRootMonomial R A

/-- The linear extension of `J_R` to a same-order signed packet. -/
def packetJ {n : ℕ}
    (W : SignedRootedPacket n) :
    MvPolynomial (Option ℕ) ℚ :=
  ∑ R ∈ W.support, (W R : ℚ) • openRootForestPolynomial R

abbrev InnerStatePolynomial := MvPolynomial (Fin 2) ℚ
abbrev StatePolynomial := Polynomial InnerStatePolynomial

def xVariable : InnerStatePolynomial := MvPolynomial.X 0
def qVariable : InnerStatePolynomial := MvPolynomial.X 1

/-- `e = n - 1 - length(lambda)` and `c(lambda)` counts parts at least two. -/
def forestExponent (n : ℕ) (lambda : Multiset ℕ) : ℕ :=
  n - 1 - lambda.card

def coveredCount (lambda : Multiset ℕ) : ℕ :=
  (lambda.filter (fun s => 2 ≤ s)).card

def rootCoveredQSum (a : ℕ) (lambda : Multiset ℕ) : InnerStatePolynomial :=
  ((a ::ₘ lambda).filter (fun s => 2 ≤ s)).map
    (fun s => qVariable ^ (s - 1)) |>.sum

def nonrootCoveredQSum (lambda : Multiset ℕ) : InnerStatePolynomial :=
  (lambda.filter (fun s => 2 ≤ s)).map
    (fun s => qVariable ^ (s - 1)) |>.sum

def markedExponent (a : ℕ) (lambda : Multiset ℕ) : ℕ :=
  coveredCount lambda + (if 2 ≤ a then 1 else 0) - 1

/-- The six coefficientwise marked-state monomials attached to `z^a x_lambda`.
The outer polynomial variable is `y`; the inner variables are `x` and `q`. -/
def cStateMonomial (n a : ℕ) (lambda : Multiset ℕ) : StatePolynomial :=
  Polynomial.C (xVariable ^ forestExponent n lambda) *
    Polynomial.X ^ (coveredCount lambda + if 2 ≤ a then 1 else 0)

def dStateMonomial (n a : ℕ) (lambda : Multiset ℕ) : StatePolynomial :=
  Polynomial.C (xVariable ^ forestExponent n lambda) *
    Polynomial.X ^ coveredCount lambda

def vStateMonomial (n a : ℕ) (lambda : Multiset ℕ) : StatePolynomial :=
  Polynomial.C (if a = 1 then xVariable ^ forestExponent n lambda else 0) *
    Polynomial.X ^ coveredCount lambda

def rStateMonomial (n a : ℕ) (lambda : Multiset ℕ) : StatePolynomial :=
  Polynomial.C
      (xVariable ^ forestExponent n lambda * qVariable ^ (a - 1)) *
    Polynomial.X ^ coveredCount lambda

def mStateMonomial (n a : ℕ) (lambda : Multiset ℕ) : StatePolynomial :=
  Polynomial.C
      (xVariable ^ forestExponent n lambda * rootCoveredQSum a lambda) *
    Polynomial.X ^ markedExponent a lambda

def bStateMonomial (n a : ℕ) (lambda : Multiset ℕ) : StatePolynomial :=
  Polynomial.C
      (xVariable ^ forestExponent n lambda * nonrootCoveredQSum lambda) *
    Polynomial.X ^ (coveredCount lambda - 1)

/-- Sum one coefficientwise state monomial over all selected edge sets. -/
def stateAggregate {n : ℕ} (R : RootedTree n)
    (term : ℕ → ℕ → Multiset ℕ → StatePolynomial) : StatePolynomial :=
  ∑ A ∈ R.1.1.edgeFinset.powerset,
    term n (rootComponentOrder R A) (nonrootComponentOrders R A)

def stateC {n : ℕ} (R : RootedTree n) : StatePolynomial :=
  stateAggregate R cStateMonomial

def stateD {n : ℕ} (R : RootedTree n) : StatePolynomial :=
  stateAggregate R dStateMonomial

def stateV {n : ℕ} (R : RootedTree n) : StatePolynomial :=
  stateAggregate R vStateMonomial

def stateM {n : ℕ} (R : RootedTree n) : StatePolynomial :=
  stateAggregate R mStateMonomial

def stateR {n : ℕ} (R : RootedTree n) : StatePolynomial :=
  stateAggregate R rStateMonomial

def stateB {n : ℕ} (R : RootedTree n) : StatePolynomial :=
  stateAggregate R bStateMonomial

/-- The six state aggregates extended linearly to a signed packet. -/
def packetState {n : ℕ} (W : SignedRootedPacket n)
    (state : RootedTree n → StatePolynomial) : StatePolynomial :=
  ∑ R ∈ W.support, (W R : ℚ) • state R

/-- The specialization `S_bar = S|_(y=1)`. -/
def stateAtYOne (S : StatePolynomial) : InnerStatePolynomial :=
  S.eval 1

/-- The tangent specialization `S_dot = (partial_y S)|_(y=1)`. -/
def stateYDerivativeAtOne (S : StatePolynomial) : InnerStatePolynomial :=
  (Polynomial.derivative S).eval 1

def tangentC {n : ℕ} (W : SignedRootedPacket n) : InnerStatePolynomial :=
  stateYDerivativeAtOne (packetState W stateC)

def tangentD {n : ℕ} (W : SignedRootedPacket n) : InnerStatePolynomial :=
  stateYDerivativeAtOne (packetState W stateD)

def tangentM {n : ℕ} (W : SignedRootedPacket n) : InnerStatePolynomial :=
  stateYDerivativeAtOne (packetState W stateM)

def tangentR {n : ℕ} (W : SignedRootedPacket n) : InnerStatePolynomial :=
  stateYDerivativeAtOne (packetState W stateR)

def tangentB {n : ℕ} (W : SignedRootedPacket n) : InnerStatePolynomial :=
  stateYDerivativeAtOne (packetState W stateB)

/-- The independently specified first marked-moment coefficient of one
`z^a x_lambda` state. -/
def firstMarkedMomentMonomial (n a : ℕ) (lambda : Multiset ℕ) :
    InnerStatePolynomial :=
  (markedExponent a lambda : ℚ) •
    (xVariable ^ forestExponent n lambda * rootCoveredQSum a lambda)

/-- The first marked moment on one rooted tree, before identifying it with the
`tangent` of the aggregate `M` state. -/
def firstMarkedMoment {n : ℕ} (R : RootedTree n) : InnerStatePolynomial :=
  ∑ A ∈ R.1.1.edgeFinset.powerset,
    firstMarkedMomentMonomial n (rootComponentOrder R A)
      (nonrootComponentOrders R A)

/-- The same first marked moment extended linearly to a signed packet. -/
def firstMarkedMomentPacket {n : ℕ}
    (W : SignedRootedPacket n) : InnerStatePolynomial :=
  ∑ R ∈ W.support, (W R : ℚ) • firstMarkedMoment R

def aggregateC {n : ℕ} (W : SignedRootedPacket n) : StatePolynomial :=
  packetState W stateC

def aggregateD {n : ℕ} (W : SignedRootedPacket n) : StatePolynomial :=
  packetState W stateD

def aggregateV {n : ℕ} (W : SignedRootedPacket n) : StatePolynomial :=
  packetState W stateV

def aggregateM {n : ℕ} (W : SignedRootedPacket n) : StatePolynomial :=
  packetState W stateM

def aggregateR {n : ℕ} (W : SignedRootedPacket n) : StatePolynomial :=
  packetState W stateR

def aggregateB {n : ℕ} (W : SignedRootedPacket n) : StatePolynomial :=
  packetState W stateB

/-- Claim 51680: the first marked moment is the packet-linear `M_dot`, and
`J(W)=0` blinds all six aggregate states and the displayed tangent aggregates. -/
def aggregateTangentKernel_claim51680 : Prop :=
  ∀ (n : ℕ) (W : SignedRootedPacket n),
    firstMarkedMomentPacket W = tangentM W ∧
      (packetJ W = 0 →
        aggregateC W = 0 ∧
          aggregateD W = 0 ∧
            aggregateV W = 0 ∧
              aggregateM W = 0 ∧
                aggregateR W = 0 ∧
                  aggregateB W = 0 ∧
                    tangentC W = 0 ∧
                      tangentD W = 0 ∧
                        tangentM W = 0 ∧
                          tangentR W = 0 ∧
                            tangentB W = 0 ∧
                              firstMarkedMomentPacket W = 0)

end

end MathlibPlus.Open.ResearchFormalization.R3893Claim51680
