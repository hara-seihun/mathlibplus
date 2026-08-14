import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

noncomputable section
open Classical
open scoped BigOperators

/-- The finite edge universe used to enumerate edge subsets. -/
def uEdgeUniverse {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) : Finset (Sym2 V) :=
  F.edgeSet.toFinite.toFinset

def uReachable {V : Type} (A : Finset (Sym2 V)) (u v : V) : Prop :=
  Relation.ReflTransGen (fun x y : V => Sym2.mk x y ∈ A) u v

def uComponent {V : Type} [Fintype V] [DecidableEq V]
    (A : Finset (Sym2 V)) (v : V) : Finset V :=
  Finset.univ.filter (uReachable A v)

def uComponents {V : Type} [Fintype V] [DecidableEq V]
    (A : Finset (Sym2 V)) : Finset (Finset V) :=
  Finset.univ.image (uComponent A)

/-- The forest U-polynomial from edge subsets and connected components. -/
def forestUPolynomial {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) : MvPolynomial ℕ ℤ :=
  Finset.sum (Finset.powerset (uEdgeUniverse F)) (fun A =>
    Finset.prod (uComponents A) (fun C => MvPolynomial.X C.card))

/-- Formal partial differentiation in the variable `x₁`. -/
def partialXOne (p : MvPolynomial ℕ ℤ) : MvPolynomial ℕ ℤ :=
  Finset.sum p.support (fun d =>
    if h : d 1 = 0 then 0 else
      MvPolynomial.monomial (d - Finsupp.single 1 1)
        (MvPolynomial.coeff d p * (d 1 : ℤ)))

def markedSingletonPolynomial {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) : MvPolynomial ℕ ℤ :=
  partialXOne (forestUPolynomial F)

def deletedVertexGraph {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (v : V) : SimpleGraph {w // w ≠ v} :=
  SimpleGraph.induce {w | w ≠ v} F

/-- The U-polynomial and marked-singleton derivative identity. -/
def claim_20297 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V), F.IsAcyclic →
    markedSingletonPolynomial F =
      Finset.sum (Finset.univ : Finset V)
        (fun v => forestUPolynomial (deletedVertexGraph F v))

def tripleLegLength (a b c : ℕ) (i : Fin 3) : ℕ :=
  if i.val = 0 then a else if i.val = 1 then b else c

def quadrupleLegLength (a b c d : ℕ) (i : Fin 4) : ℕ :=
  if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else d

abbrev SpiderVertex {l : ℕ} (legs : Fin l → ℕ) :=
  Option (Σ i : Fin l, Fin (legs i))

def spiderGraph {l : ℕ} (legs : Fin l → ℕ) :
    SimpleGraph (SpiderVertex legs) :=
  SimpleGraph.fromRel (fun a b =>
    match a, b with
    | none, none => False
    | none, some q => q.2.val = 0
    | some q, none => q.2.val = 0
    | some q, some r =>
        q.1 = r.1 ∧
          (q.2.val + 1 = r.2.val ∨ r.2.val + 1 = q.2.val))

def spiderU (legs : Fin l → ℕ) : MvPolynomial ℕ ℤ :=
  forestUPolynomial (spiderGraph legs)

def spiderMarked (legs : Fin l → ℕ) : MvPolynomial ℕ ℤ :=
  markedSingletonPolynomial (spiderGraph legs)

/-- The order-seven spider U-polynomial trade. -/
def claim_20303 : Prop :=
  spiderU (tripleLegLength 1 1 4) -
      2 * spiderU (tripleLegLength 1 2 3) +
      spiderU (tripleLegLength 2 2 2) = 0

/-- One inward augmentation gives the stated nonzero marked-polynomial defect. -/
def claim_20306 : Prop :=
  let defect :=
    spiderMarked (quadrupleLegLength 1 1 1 4) -
      2 * spiderMarked (quadrupleLegLength 1 1 2 3) +
      spiderMarked (quadrupleLegLength 1 2 2 2)
  defect =
      -3 * MvPolynomial.X 1 ^ 2 * MvPolynomial.X 5 +
      4 * MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 4 +
      2 * MvPolynomial.X 1 * MvPolynomial.X 3 ^ 2 -
      3 * MvPolynomial.X 2 ^ 2 * MvPolynomial.X 3 -
      2 * MvPolynomial.X 2 * MvPolynomial.X 5 +
      2 * MvPolynomial.X 3 * MvPolynomial.X 4 ∧
    defect ≠ 0

end
end MathlibPlus.Open.ResearchFormalizationBatch
