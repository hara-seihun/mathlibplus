import Mathlib

noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators Topology

namespace MathlibPlus.Open.Combinatorics.LeafDeck

def graphG1Edges : Set (Sym2 (Fin 5)) :=
  {s((0 : Fin 5), (3 : Fin 5)), s((0 : Fin 5), (4 : Fin 5)),
   s((1 : Fin 5), (4 : Fin 5)), s((2 : Fin 5), (4 : Fin 5)),
   s((3 : Fin 5), (4 : Fin 5))}

def graphG2Edges : Set (Sym2 (Fin 5)) :=
  {s((0 : Fin 5), (3 : Fin 5)), s((1 : Fin 5), (3 : Fin 5)),
   s((0 : Fin 5), (4 : Fin 5)), s((2 : Fin 5), (4 : Fin 5)),
   s((3 : Fin 5), (4 : Fin 5))}

def graphHEdges : Set (Sym2 (Fin 4)) :=
  {s((0 : Fin 4), (1 : Fin 4)), s((1 : Fin 4), (2 : Fin 4)),
   s((0 : Fin 4), (2 : Fin 4)), s((0 : Fin 4), (3 : Fin 4))}

def graphG1 : SimpleGraph (Fin 5) :=
  SimpleGraph.fromEdgeSet graphG1Edges

def graphG2 : SimpleGraph (Fin 5) :=
  SimpleGraph.fromEdgeSet graphG2Edges

def graphH : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet graphHEdges

noncomputable def finiteDegree (G : SimpleGraph (Fin 5)) (v : Fin 5) : ℕ := by
  classical
  exact (Finset.univ.filter (fun w => G.Adj v w)).card

noncomputable def graphEdgeCard (G : SimpleGraph (Fin 5)) : ℕ := by
  classical
  letI : Fintype {e : Sym2 (Fin 5) // e ∈ G.edgeSet} := Fintype.ofFinite _
  exact Fintype.card {e : Sym2 (Fin 5) // e ∈ G.edgeSet}

def unicyclicOnFive (G : SimpleGraph (Fin 5)) : Prop :=
  G.Connected ∧ graphEdgeCard G = 5

noncomputable def graphLeaves (G : SimpleGraph (Fin 5)) : Finset (Fin 5) := by
  classical
  exact Finset.univ.filter (fun v => finiteDegree G v = 1)

noncomputable def degreeMultiset (G : SimpleGraph (Fin 5)) : Multiset ℕ :=
  Multiset.map (finiteDegree G) (Finset.univ : Finset (Fin 5)).1

def leafDeckWitness (G : SimpleGraph (Fin 5)) : Prop :=
  (graphLeaves G).card = 2 ∧
    ∀ v : Fin 5, v ∈ graphLeaves G →
      Nonempty (SimpleGraph.Iso
        (G.induce {w : Fin 5 | w ≠ v}) graphH)

def claim14298 : Prop :=
  unicyclicOnFive graphG1 ∧ unicyclicOnFive graphG2 ∧
    leafDeckWitness graphG1 ∧ leafDeckWitness graphG2 ∧
    degreeMultiset graphG1 = Multiset.ofList [4, 2, 2, 1, 1] ∧
    degreeMultiset graphG2 = Multiset.ofList [3, 3, 2, 1, 1] ∧
    ¬ Nonempty (SimpleGraph.Iso graphG1 graphG2)

end MathlibPlus.Open.Combinatorics.LeafDeck
