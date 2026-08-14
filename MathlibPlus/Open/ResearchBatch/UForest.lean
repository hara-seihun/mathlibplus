import Mathlib
import MathlibPlus.GraphTheory.Claim28295

namespace MathlibPlus.Open.ResearchBatch.UForest

open scoped Sym2 BigOperators

/-- The component partition of the spanning graph represented by an edge set. -/
noncomputable def forestPartition {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset (Sym2 V)) : Nat.Partition (Fintype.card V) :=
  MathlibPlus.GraphTheory.Claim28295.componentPartition
    (SimpleGraph.fromEdgeSet (S : Set (Sym2 V)))

/-- Actual edge-subset fibres for a component-order partition. -/
noncomputable def edgeSubsetFibre {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (part : Nat.Partition (Fintype.card V)) :
    Set (Finset (Sym2 V)) :=
  {S | (S : Set (Sym2 V)) ⊆ H.edgeSet ∧ forestPartition S = part}

/-- The undecorated edge-subset `U` polynomial. -/
noncomputable def edgeSubsetUPolynomial
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) :
    MvPolynomial (Nat.Partition (Fintype.card V)) ℕ := by
  classical
  exact ∑ S : Finset (Sym2 V),
    if (S : Set (Sym2 V)) ⊆ H.edgeSet then
      MvPolynomial.X (forestPartition S)
    else 0

/--
The exact coefficient decomposition of the `U` polynomial by actual spanning
edge-subset fibres.
-/
def claim59092_exactEdgeSubsetFibreDecomposition : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V),
    H.IsTree →
    edgeSubsetUPolynomial H =
      ∑ part : Nat.Partition (Fintype.card V),
        (Set.ncard (edgeSubsetFibre H part) : ℕ) • MvPolynomial.X part

end MathlibPlus.Open.ResearchBatch.UForest
