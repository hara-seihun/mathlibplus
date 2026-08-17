import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0872

noncomputable section

private abbrev Arm (V : Type*) := V × V

private def touchedBlockCount {V : Type*} [Fintype V] [DecidableEq V]
    (Z : V → Finset (Arm V)) (A : Finset (Arm V)) : ℕ :=
  (Finset.univ.filter (fun v => (A ∩ Z v).Nonempty)).card

private def branchDefect {V : Type*} [Fintype V] [DecidableEq V]
    (Z : V → Finset (Arm V)) (A : Finset (Arm V)) : ℤ :=
  (A.card : ℤ) - (touchedBlockCount Z A : ℤ)

private def graphDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) : ℕ :=
  Nat.card {w : V // G.Adj v w}

private def reducedSubcubicArmBlocks
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Z : V → Finset (Arm V)) : Prop :=
  G.IsTree ∧
    (∀ v : V, graphDegree G v ≤ 3) ∧
    (∀ v : V, graphDegree G v ≠ 2) ∧
    (∀ v w : V, v ≠ w → Disjoint (Z v) (Z w)) ∧
    (∀ v : V, ∀ e : Arm V,
      e ∈ Z v ↔
        graphDegree G v = 3 ∧ e.1 = v ∧ G.Adj e.1 e.2 ∧
          graphDegree G e.2 = 1)

private def zeroDefectComplex {V : Type*} [Fintype V] [DecidableEq V]
    (Z : V → Finset (Arm V)) : Set (Finset (Arm V)) :=
  {A | A ⊆ (Finset.univ : Finset V).biUnion Z ∧ branchDefect Z A = 0}

private def partitionMatroidComplex
    {V : Type*} [Fintype V] [DecidableEq V]
    (Z : V → Finset (Arm V)) : Set (Finset (Arm V)) :=
  {A | A ⊆ (Finset.univ : Finset V).biUnion Z ∧
    ∀ v : V, (A ∩ Z v).card ≤ 1}

private abbrev ActiveBranch (V : Type*) [Fintype V] [DecidableEq V]
    (Z : V → Finset (Arm V)) :=
  {v : V // (Z v).Nonempty}

/-- The join is represented by independent choices of a face (empty or a
singleton) in each nonempty discrete block, followed by their disjoint union.
It is not defined by reusing the partition-matroid predicate. -/
private def blockJoinComplex
    {V : Type*} [Fintype V] [DecidableEq V]
    (Z : V → Finset (Arm V)) : Set (Finset (Arm V)) :=
  {A | ∃ choices : ActiveBranch V Z → Finset (Arm V),
    (∀ v, choices v ⊆ Z v.1) ∧
      (∀ v, (choices v).card ≤ 1) ∧
      (∀ v w, v ≠ w → Disjoint (choices v) (choices w)) ∧
      A = (Finset.univ : Finset (ActiveBranch V Z)).biUnion choices}

/-- Claim 29632: the zero-defect deletion complex is the partition-matroid
independence complex and, independently, the join of the nonempty discrete
unit-arm blocks. -/
def claim29632 : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Z : V → Finset (Arm V)),
    reducedSubcubicArmBlocks G Z →
      zeroDefectComplex Z = partitionMatroidComplex Z ∧
        partitionMatroidComplex Z = blockJoinComplex Z

end

end MathlibPlus.Open.ResearchFormalization.R0872
