import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R5111.Claim57209

open Classical
open scoped BigOperators

noncomputable section

abbrev Coeff := MvPolynomial (Fin 3) ℤ

 def xVar : Coeff := MvPolynomial.X (0 : Fin 3)

def yVar : Coeff := MvPolynomial.X (1 : Fin 3)

def zVar : Coeff := MvPolynomial.X (2 : Fin 3)

def qMatrix : Matrix (Fin 2) (Fin 2) Coeff :=
  !![1, yVar; yVar, zVar]

def wMatrix : Matrix (Fin 2) (Fin 2) Coeff :=
  !![1, 0; 0, xVar]

def kMatrix : Matrix (Fin 2) (Fin 2) Coeff :=
  qMatrix * wMatrix * qMatrix

def stateWeight (s : Fin 2) : Coeff :=
  if s = 0 then 1 else xVar

def canonicalLess {V : Type*} [Fintype V] (u v : V) : Prop :=
  (Fintype.equivFin V u).val < (Fintype.equivFin V v).val

def edgePairs {V : Type*} [Fintype V]
    (T : SimpleGraph V) : Finset (V × V) :=
  (Finset.univ : Finset (V × V)).filter
    (fun e => canonicalLess e.1 e.2 ∧ T.Adj e.1 e.2)

def assignmentWeight {V : Type*} [Fintype V]
    (T : SimpleGraph V) (σ : V → Fin 2) : Coeff :=
  (∏ v : V, stateWeight (σ v)) *
    (∏ e ∈ edgePairs T, qMatrix (σ e.1) (σ e.2))

/-- A finite rooted packet in the central-edge construction is a rooted tree. -/
structure RootedTree where
  n : ℕ
  graph : SimpleGraph (Fin n)
  root : Fin n
  isTree : graph.IsTree

abbrev RootedPacket := RootedTree

def rootedMessage (R : RootedPacket) (s : Fin 2) : Coeff :=
  ∑ σ : Fin R.n → Fin 2,
    if σ R.root = s then assignmentWeight R.graph σ else 0

def messageVector (R : RootedPacket) : Fin 2 → Coeff :=
  rootedMessage R

def aContraction (K : Matrix (Fin 2) (Fin 2) Coeff)
    (R S : RootedPacket) : Coeff :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    messageVector R i * K i j * messageVector S j

def generalizedDegree {V : Type*} [Fintype V]
    (T : SimpleGraph V) : Coeff :=
  ∑ σ : V → Fin 2, assignmentWeight T σ

abbrev JoinedVertex (U V C D : RootedPacket) :=
  Fin 2 ⊕ (Fin U.n ⊕ (Fin V.n ⊕ (Fin C.n ⊕ Fin D.n)))

def joinedRelation (cross : Bool)
    (U V C D : RootedPacket) :
    JoinedVertex U V C D → JoinedVertex U V C D → Prop :=
  fun a b =>
    match a, b with
    | Sum.inl i, Sum.inl j => i ≠ j
    | Sum.inr (Sum.inl u), Sum.inr (Sum.inl u') => U.graph.Adj u u'
    | Sum.inr (Sum.inr (Sum.inl v)), Sum.inr (Sum.inr (Sum.inl v')) =>
        V.graph.Adj v v'
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl c))),
        Sum.inr (Sum.inr (Sum.inr (Sum.inl c'))) => C.graph.Adj c c'
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr d))),
        Sum.inr (Sum.inr (Sum.inr (Sum.inr d'))) => D.graph.Adj d d'
    | Sum.inl i, Sum.inr (Sum.inl u) => i = 0 ∧ u = U.root
    | Sum.inl i, Sum.inr (Sum.inr (Sum.inl v)) => i = 1 ∧ v = V.root
    | Sum.inl i,
        Sum.inr (Sum.inr (Sum.inr (Sum.inl c))) =>
        (if cross = true then i = 1 else i = 0) ∧ c = C.root
    | Sum.inl i,
        Sum.inr (Sum.inr (Sum.inr (Sum.inr d))) =>
        (if cross = true then i = 0 else i = 1) ∧ d = D.root
    | _, _ => False

def switchGraph (cross : Bool)
    (U V C D : RootedPacket) : SimpleGraph (JoinedVertex U V C D) :=
  SimpleGraph.fromRel (joinedRelation cross U V C D)

/-- The exact two-state central-edge message identity. -/
def claim57209 : Prop :=
  let Q : Matrix (Fin 2) (Fin 2) Coeff := qMatrix
  let W : Matrix (Fin 2) (Fin 2) Coeff := wMatrix
  let K : Matrix (Fin 2) (Fin 2) Coeff := Q * W * Q
  (K 0 0 = 1 + xVar * yVar ^ 2 ∧
      K 0 1 = yVar + xVar * yVar * zVar ∧
      K 1 1 = yVar ^ 2 + xVar * zVar ^ 2) ∧
    (∀ U V C D : RootedPacket,
      generalizedDegree (switchGraph false U V C D) -
          generalizedDegree (switchGraph true U V C D) =
        yVar *
          (aContraction K U C * aContraction K V D -
            aContraction K U D * aContraction K V C))

end
end MathlibPlus.Open.ResearchFormalization.R5111.Claim57209
