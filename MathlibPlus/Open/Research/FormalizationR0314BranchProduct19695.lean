import Mathlib

namespace MathlibPlus.Open.Research.FormalizationR0314.BranchProduct19695

noncomputable section

open Classical
open scoped BigOperators

private abbrev PottsPoly (m : ℕ) :=
  MvPolynomial (Fin m ⊕ (Fin m ⊕ Unit)) ℤ

private def xVariable {m : ℕ} (i : Fin m) : PottsPoly m :=
  MvPolynomial.X (Sum.inl i)

private def zVariable {m : ℕ} (i : Fin m) : PottsPoly m :=
  MvPolynomial.X (Sum.inr (Sum.inl i))

private def yVariable {m : ℕ} : PottsPoly m :=
  MvPolynomial.X (Sum.inr (Sum.inr Unit.unit))

private def stateWeight {m : ℕ} (s : Fin (m + 1)) : PottsPoly m :=
  if h : s = 0 then 1 else xVariable (Fin.pred s h)

private def interactionOnSym2 {m : ℕ} (e : Sym2 (Fin (m + 1))) : PottsPoly m :=
  if e = Sym2.mk 0 0 then 1
  else if h : ∃ i : Fin m, e = Sym2.mk (Fin.succ i) (Fin.succ i) then
    zVariable (Classical.choose h)
  else yVariable

private def interaction {m : ℕ} (s t : Fin (m + 1)) : PottsPoly m :=
  interactionOnSym2 (Sym2.mk s t)

private def edgeInteraction {V : Type*} [Fintype V] [DecidableEq V]
    {m : ℕ} (σ : V → Fin (m + 1)) (e : Sym2 V) : PottsPoly m :=
  interactionOnSym2 (Sym2.map σ e)

private def edgePairs {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : Finset (Sym2 V) :=
  T.edgeSet.toFinite.toFinset

private def assignmentWeight {V : Type*} [Fintype V] [DecidableEq V]
    {m : ℕ} (T : SimpleGraph V) (σ : V → Fin (m + 1)) : PottsPoly m :=
  (∏ v : V, stateWeight (σ v)) *
    (∏ e ∈ edgePairs T, edgeInteraction σ e)

private def message {V : Type*} [Fintype V] [DecidableEq V]
    (m : ℕ) (T : SimpleGraph V) (r : V) (s : Fin (m + 1)) : PottsPoly m :=
  ∑ σ : V → Fin (m + 1),
    if σ r = s then assignmentWeight T σ else 0

private def pinnedFactor {V : Type*} [Fintype V] [DecidableEq V]
    (m : ℕ) (T : SimpleGraph V) (r : V) (s : Fin (m + 1)) : PottsPoly m :=
  ∑ t : Fin (m + 1), interaction s t * message m T r t

private structure RootedBranch (V : Type*) where
  carrier : Finset V
  root : {v // v ∈ carrier}

private def branchGraph {V : Type*}
    (T : SimpleGraph V) (B : RootedBranch V) : SimpleGraph {v // v ∈ B.carrier} :=
  T.induce (B.carrier : Set V)

private def rootedBranchAt {V : Type*} [DecidableEq V]
    (T : SimpleGraph V) (r : V) (B : RootedBranch V) : Prop :=
  (branchGraph T B).IsTree ∧
    (∀ v, v ∈ B.carrier → v ≠ r) ∧
    T.Adj r B.root.1 ∧
    (∀ v, v ∈ B.carrier → (T.Adj r v ↔ v = B.root.1)) ∧
    (∀ v, v ∈ B.carrier → ∀ u, u ≠ r → u ∉ B.carrier → ¬ T.Adj v u)

private def rootedBranchDecomposition {V : Type*} [DecidableEq V]
    (T : SimpleGraph V) (r : V) (d : ℕ)
    (B : Fin d → RootedBranch V) : Prop :=
  (∀ i, rootedBranchAt T r (B i)) ∧
    (∀ i j, i ≠ j → ∀ v, v ∈ (B i).carrier → v ∉ (B j).carrier) ∧
    (∀ v, v ≠ r → ∃ i, v ∈ (B i).carrier)

def exactBranchProductRecursion19695 : Prop :=
  ∀ (m : ℕ), 1 ≤ m →
    ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (T : SimpleGraph V) (r : V),
      T.IsTree →
      ∀ (d : ℕ) (B : Fin d → RootedBranch V),
        rootedBranchDecomposition T r d B →
        ∀ s : Fin (m + 1),
          message m T r s =
            stateWeight s *
              ∏ i : Fin d,
                pinnedFactor m (branchGraph T (B i)) (B i).root s

end

end MathlibPlus.Open.Research.FormalizationR0314.BranchProduct19695
