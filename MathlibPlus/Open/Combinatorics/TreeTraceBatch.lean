import Mathlib

namespace MathlibPlus.Open.TreeTraceBatch

noncomputable section

/-- The finite vertex sets that are exactly the connected components of a graph. -/
def componentSets {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset (Finset V) :=
  letI : DecidablePred (fun C : Finset V =>
      C.Nonempty ∧
        (∀ u ∈ C, ∀ v ∈ C, G.Reachable u v) ∧
        (∀ u ∈ C, ∀ v, G.Reachable u v → v ∈ C)) :=
    Classical.decPred _
  Finset.filter
    (fun C : Finset V =>
      C.Nonempty ∧
        (∀ u ∈ C, ∀ v ∈ C, G.Reachable u v) ∧
        (∀ u ∈ C, ∀ v, G.Reachable u v → v ∈ C))
    (Finset.powerset (Finset.univ : Finset V))

/-- The unordered partition of component orders. -/
def componentOrders {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Multiset ℕ :=
  (componentSets G).1.map Finset.card

/-- Edge subsets of a finite graph, represented by spanning subgraphs. -/
def edgeSubgraphs {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : Finset (SimpleGraph V) :=
  letI : DecidablePred (fun H : SimpleGraph V => H ≤ T) := Classical.decPred _
  Finset.filter (fun H : SimpleGraph V => H ≤ T) Finset.univ

/-- The scalar formal polynomial whose monomial index is the unordered partition. -/
def tracePolynomial {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : AddMonoidAlgebra ℤ (Multiset ℕ) :=
  Finset.sum (edgeSubgraphs T)
    (fun h => AddMonoidAlgebra.single (componentOrders h) (1 : ℤ))

/-- The graph obtained by deleting one vertex while retaining the original carrier. -/
def removeVertex {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (c : V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => u ≠ c ∧ v ≠ c ∧ T.Adj u v)

/-- The usual centroid condition, expressed by component orders after deletion. -/
def isCentroid {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (c : V) : Prop :=
  ∀ C ∈ componentSets (removeVertex T c), c ∉ C →
    2 * C.card ≤ Fintype.card V

def hasUniqueCentroidAt {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (c : V) : Prop :=
  isCentroid T c ∧ ∀ d : V, isCentroid T d → d = c

def hasUniqueCentroid {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : Prop :=
  ∃! c : V, isCentroid T c

/-- The component containing the distinguished centroid in a spanning subgraph. -/
def centroidComponent {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (c : V) : Finset V :=
  letI : DecidablePred (fun v : V => H.Reachable c v) := Classical.decPred _
  Finset.filter (fun v : V => H.Reachable c v) Finset.univ

/-- The complete centroid-component flag. -/
def centroidFlag {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (c : V) (part : Multiset ℕ) (q : ℕ) : ℕ :=
  letI : DecidablePred (fun H : SimpleGraph V =>
      componentOrders H = part ∧ (centroidComponent H c).card = q) :=
    Classical.decPred _
  (Finset.filter
      (fun H : SimpleGraph V =>
        componentOrders H = part ∧ (centroidComponent H c).card = q)
      (edgeSubgraphs T)).card

/-- The finite form of the sum of a flag row; all larger rows are zero. -/
def centroidFlagRowSum {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (c : V) (part : Multiset ℕ) : ℕ :=
  Finset.sum Finset.univ (fun q : Fin (Fintype.card V + 1) =>
    centroidFlag T c part q.val)

/-- Claim 60513: scalar coefficients are row sums of the complete flag. -/
def admitted_60513 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (c : V),
    T.IsTree → hasUniqueCentroidAt T c →
      ∀ part : Multiset ℕ,
        (AddMonoidAlgebra.coeff (tracePolynomial T)) part =
          (centroidFlagRowSum T c part : ℤ)

abbrev SpiderVertex (a b c : ℕ) := Unit ⊕ (Fin a ⊕ Fin b ⊕ Fin c)

def spiderCenter (a b c : ℕ) : SpiderVertex a b c :=
  Sum.inl ()

/-- The unrooted three-legged spider with the displayed leg lengths. -/
def spider (a b c : ℕ) : SimpleGraph (SpiderVertex a b c) :=
  SimpleGraph.fromRel (fun u v =>
    match u, v with
    | Sum.inl _, Sum.inr (Sum.inl i) => i.val = 0
    | Sum.inl _, Sum.inr (Sum.inr (Sum.inl j)) => j.val = 0
    | Sum.inl _, Sum.inr (Sum.inr (Sum.inr k)) => k.val = 0
    | Sum.inr (Sum.inl i), Sum.inr (Sum.inl j) =>
        i.val + 1 = j.val ∨ j.val + 1 = i.val
    | Sum.inr (Sum.inr (Sum.inl i)), Sum.inr (Sum.inr (Sum.inl j)) =>
        i.val + 1 = j.val ∨ j.val + 1 = i.val
    | Sum.inr (Sum.inr (Sum.inr i)), Sum.inr (Sum.inr (Sum.inr j)) =>
        i.val + 1 = j.val ∨ j.val + 1 = i.val
    | _, _ => False)

def spiderA : SimpleGraph (SpiderVertex 1 1 4) := spider 1 1 4
def spiderB : SimpleGraph (SpiderVertex 1 2 3) := spider 1 2 3
def spiderC : SimpleGraph (SpiderVertex 2 2 2) := spider 2 2 2

/-- Claim 60514: the three order-seven spiders satisfy the exact scalar relation. -/
def admitted_60514 : Prop :=
  spiderA.IsTree ∧ spiderB.IsTree ∧ spiderC.IsTree ∧
    Fintype.card (SpiderVertex 1 1 4) = 7 ∧
    Fintype.card (SpiderVertex 1 2 3) = 7 ∧
    Fintype.card (SpiderVertex 2 2 2) = 7 ∧
    hasUniqueCentroid spiderA ∧
    hasUniqueCentroid spiderB ∧
    hasUniqueCentroid spiderC ∧
    tracePolynomial spiderA - (2 : ℤ) • tracePolynomial spiderB +
        tracePolynomial spiderC = 0

end

end MathlibPlus.Open.TreeTraceBatch
