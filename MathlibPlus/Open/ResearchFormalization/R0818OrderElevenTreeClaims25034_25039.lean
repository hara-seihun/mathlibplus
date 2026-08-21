-- UNVERIFIED (downstream): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib
import MathlibPlus.Combinatorics.Claim25033

open scoped Sym2

namespace MathlibPlus.Open.ResearchFormalization.R0818OrderElevenTree

noncomputable section

/-- The exact edge set from Claim 25033. -/
def orderElevenEdges : Finset (Sym2 (Fin 11)) :=
  {s(0, 1), s(1, 2), s(2, 3), s(0, 6), s(6, 4),
   s(4, 5), s(5, 7), s(6, 8), s(7, 9), s(7, 10)}

def orderElevenTree : SimpleGraph (Fin 11) :=
  SimpleGraph.fromEdgeSet (orderElevenEdges : Set (Sym2 (Fin 11)))

def rootedGraphAutomorphism (u v : Fin 11) : Prop :=
  ∃ e : Equiv.Perm (Fin 11),
    e u = v ∧ ∀ x y, orderElevenTree.Adj x y ↔
      orderElevenTree.Adj (e x) (e y)

def deletedForest (v : Fin 11) : SimpleGraph {w : Fin 11 // w ≠ v} :=
  orderElevenTree.induce {w : Fin 11 | w ≠ v}

/-- A two-component split of an edge-deleted graph, with the component
orders kept as finite vertex subsets rather than inferred from a label. -/
def fiveSixComponentSplit (e : Sym2 (Fin 11)) : Prop := by
  classical
  let G := orderElevenTree.deleteEdges ({e} : Set (Sym2 (Fin 11)))
  exact ∃ A B : Finset (Fin 11),
    A.card = 5 ∧ B.card = 6 ∧
    Disjoint A B ∧ A ∪ B = Finset.univ ∧
    (∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) ∧
    (G.induce (A : Set (Fin 11))).Connected ∧
    (G.induce (B : Set (Fin 11))).Connected

def distinguishedSplitEdge : Sym2 (Fin 11) := s(6, 4)

def rootsInFiveSixSplit : Prop := by
  classical
  let G := orderElevenTree.deleteEdges
    ({distinguishedSplitEdge} : Set (Sym2 (Fin 11)))
  exact ∃ A B : Finset (Fin 11),
    A.card = 5 ∧ B.card = 6 ∧
    Disjoint A B ∧ A ∪ B = Finset.univ ∧
    (∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) ∧
    (G.induce (A : Set (Fin 11))).Connected ∧
    (G.induce (B : Set (Fin 11))).Connected ∧
    (5 ∈ A) ∧ (0 ∈ B)

/-- Claim 25034: roots `0` and `5` are not automorphic, while deleting them
from this exact tree gives isomorphic forests. -/
def deletionSimilarNonautomorphicRoots_claim25034 : Prop :=
  (¬ rootedGraphAutomorphism 0 5) ∧
  Nonempty (deletedForest 0 ≃g deletedForest 5)

/-- Claim 25039: edge `64` is the unique edge producing any `5|6` component
split, and the stated roots lie in the order-five and order-six components. -/
def uniqueFiveSixEdgeSplit_claim25039 : Prop :=
  (∀ e : Sym2 (Fin 11),
    fiveSixComponentSplit e ↔ e = distinguishedSplitEdge) ∧
  rootsInFiveSixSplit

end

end MathlibPlus.Open.ResearchFormalization.R0818OrderElevenTree
