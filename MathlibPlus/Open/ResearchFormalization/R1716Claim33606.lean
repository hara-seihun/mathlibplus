import MathlibPlus.Open.ResearchBatchR1716.UPolynomialClaims33611_33613

open scoped Classical BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1716Claim33606

noncomputable section

open MathlibPlus.Open.Combinatorics.DTreeUPolynomial

/-- Whether an edge of the fixed tree is deleted by the partition cut. -/
def crossesPartition {V : Type*} [Fintype V] [LinearOrder V]
    (P : Finset (Finset V)) (e : V × V) : Prop :=
  ¬ ∃ C ∈ P, e.1 ∈ C ∧ e.2 ∈ C

/-- The edges crossing the displayed blocks. -/
def cutEdges {V : Type*} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (P : Finset (Finset V)) : Finset (V × V) :=
  (edgePairs T).filter (crossesPartition P)

/-- The edges retained after deleting a cut subset. -/
def retainedEdges {V : Type*} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (S : Finset (V × V)) : Finset (V × V) :=
  (edgePairs T).filter (fun e => e ∉ S)

/-- The component partition of the spanning forest obtained from a cut. -/
def componentBlock {V : Type*} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (S : Finset (V × V)) (u : V) : Finset V :=
  Finset.univ.filter
    (componentRelation (retainedEdges T S) u)

/-- The finite partition into the components after the cut. -/
def componentsAfterCut {V : Type*} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (S : Finset (V × V)) : Finset (Finset V) :=
  Finset.univ.image (componentBlock T S)

/-- A connected set partition is represented by the exact component-partition
predicate on the forest left after deleting its crossing edges. -/
def connectedPartition {V : Type*} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (P : Finset (Finset V)) : Prop :=
  isComponentPartition
    (retainedEdges T (cutEdges T P)) P

/-- Claim 33606: for every finite tree, deleting the edges crossing a connected
partition and taking components gives inverse maps between connected set
partitions and subsets of the tree edge carrier; a q-block partition deletes
q-1 edges. -/
def claim33606 : Prop :=
  ∀ {V : Type*} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V),
    T.IsTree →
      (∀ P : Finset (Finset V),
        connectedPartition T P →
          cutEdges T P ⊆ edgePairs T ∧
            connectedPartition T (componentsAfterCut T (cutEdges T P)) ∧
              componentsAfterCut T (cutEdges T P) = P) ∧
      (∀ S : Finset (V × V),
        S ⊆ edgePairs T →
          connectedPartition T (componentsAfterCut T S) ∧
            cutEdges T (componentsAfterCut T S) = S) ∧
      (∀ q : ℕ, ∀ P : Finset (Finset V),
        connectedPartition T P → P.card = q →
          (cutEdges T P).card = q - 1)

end

end MathlibPlus.Open.ResearchFormalization.R1716Claim33606
