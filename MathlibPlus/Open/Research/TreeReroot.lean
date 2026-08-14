import Mathlib

namespace MathlibPlus.Open.Research.TreeReroot

open scoped BigOperators
open Classical

noncomputable section

/-- A finite rooted tree, represented on a finite labelled vertex set. -/
structure RootedTree where
  n : ℕ
  graph : SimpleGraph (Fin n)
  root : Fin n
  isTree : graph.IsTree

abbrev TreePolynomial := MvPolynomial (Fin 2) ℤ

def uVar : TreePolynomial := MvPolynomial.X 0

def vVar : TreePolynomial := MvPolynomial.X 1

def boundaryEdges (R : RootedTree) (K : Finset (Fin R.n)) : Finset (Fin R.n × Fin R.n) :=
  Finset.univ.filter (fun e =>
    e.1 ∈ K ∧ e.2 ∉ K ∧ R.graph.Adj e.1 e.2)

def inducedConnected (R : RootedTree) (K : Finset (Fin R.n)) : Prop :=
  (R.graph.induce (K : Set (Fin R.n))).Connected

/-- The rooted-tree polynomial `A_R(u,v)` from the admitted identity. -/
noncomputable def rootedA (R : RootedTree) : TreePolynomial :=
  ∑ K : Finset (Fin R.n),
    if R.root ∈ K ∧ inducedConnected R K then
      uVar ^ (K.card - 1) * vVar ^ (boundaryEdges R K).card
    else 0

/-- The rooted-tree polynomial `B_R(u,v)=v+u A_R(u,v)`. -/
def rootedB (R : RootedTree) : TreePolynomial :=
  vVar + uVar * rootedA R

def unrootedTreeIso (R S : RootedTree) : Prop :=
  Nonempty (R.graph ≃g S.graph)

def rootedTreeIso (R S : RootedTree) : Prop :=
  ∃ e : R.graph ≃g S.graph, e R.root = S.root

def sameUnrootedMultiset (E F : Multiset RootedTree) : Prop :=
  Multiset.Rel unrootedTreeIso E F

def sameRootedMultiset (E F : Multiset RootedTree) : Prop :=
  Multiset.Rel rootedTreeIso E F

def nontrivialStar (R : RootedTree) : Prop :=
  ∃ k : ℕ,
    2 ≤ k ∧ Nonempty (R.graph ≃g SimpleGraph.starGraph (0 : Fin (k + 1)))

def contextProduct (C : Multiset RootedTree) : TreePolynomial :=
  Multiset.prod (C.map rootedB)

def residualProduct (E : Multiset RootedTree) : TreePolynomial :=
  contextProduct E

def residualSum (E : Multiset RootedTree) : TreePolynomial :=
  Multiset.sum (E.map rootedA)

/-- Claim 59949: the exact pure simultaneous-reroot identity forces rooted equality. -/
def claim_59949_pureRerootObstruction : Prop :=
  ∀ (C E F : Multiset RootedTree),
    sameUnrootedMultiset E F →
    (∀ R ∈ E, nontrivialStar R) →
    (∀ R ∈ F, nontrivialStar R) →
    let Q := contextProduct C
    let ΔP := residualProduct E - residualProduct F
    let ΔA := residualSum E - residualSum F
    Q * ΔP + (vVar - 1) * ΔA = 0 →
      sameRootedMultiset E F

end

end MathlibPlus.Open.Research.TreeReroot
