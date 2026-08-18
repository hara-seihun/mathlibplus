import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0314Claim19694

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

private def interaction {m : ℕ} (s t : Fin (m + 1)) : PottsPoly m :=
  if _h : s = 0 ∧ t = 0 then 1
  else if _h : s = t then
    if hs : s = 0 then 1 else zVariable (Fin.pred s hs)
  else yVariable

private def edgeInteraction {V : Type*} [Fintype V] [DecidableEq V]
    {m : ℕ} (σ : V → Fin (m + 1)) (e : Sym2 V) : PottsPoly m :=
  let p := Quot.out e
  interaction (σ p.1) (σ p.2)

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

private def q {m : ℕ} (s t : Fin (m + 1)) : PottsPoly m :=
  interaction s t

private def phi {V : Type*} [Fintype V] [DecidableEq V]
    (m : ℕ) (T : SimpleGraph V) (r : V) (s : Fin (m + 1)) : PottsPoly m :=
  ∑ t : Fin (m + 1), q s t * message m T r t

private def parentGraph {V : Type*}
    (T : SimpleGraph V) (r : V) : SimpleGraph (Option V) :=
  SimpleGraph.fromRel (fun a b =>
    match a, b with
    | none, none => False
    | none, some v => v = r
    | some v, none => v = r
    | some v, some w => T.Adj v w)

private def extendedStateWeight {V : Type*} [Fintype V] [DecidableEq V]
    {m : ℕ} (σ : Option V → Fin (m + 1)) (v : Option V) : PottsPoly m :=
  match v with
  | none => 1
  | some _ => stateWeight (σ v)

private def extendedEdgeInteraction {V : Type*} [Fintype V] [DecidableEq V]
    {m : ℕ} (σ : Option V → Fin (m + 1))
    (e : Sym2 (Option V)) : PottsPoly m :=
  let p := Quot.out e
  interaction (σ p.1) (σ p.2)

private def externalAssignmentWeight {V : Type*} [Fintype V] [DecidableEq V]
    {m : ℕ} (T : SimpleGraph V) (r : V)
    (σ : Option V → Fin (m + 1)) : PottsPoly m :=
  (∏ v : Option V, extendedStateWeight σ v) *
    (∏ e ∈ edgePairs (parentGraph T r), extendedEdgeInteraction σ e)

private def externalParentPartition {V : Type*} [Fintype V] [DecidableEq V]
    (m : ℕ) (T : SimpleGraph V) (r : V) (s : Fin (m + 1)) : PottsPoly m :=
  ∑ σ : Option V → Fin (m + 1),
    if σ none = s then externalAssignmentWeight T r σ else 0

/-- Claim 19694: the factor obtained from root-conditioned messages by one
unweighted parent edge is the partition polynomial of that parent-augmented
rooted tree with the parent fixed in state `s`. -/
def pinnedParentFactorization_claim19694 : Prop :=
  ∀ (m : ℕ), 1 ≤ m →
    ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (T : SimpleGraph V) (r : V),
      T.IsTree →
      ∀ s : Fin (m + 1),
        phi m T r s = externalParentPartition m T r s

end

end MathlibPlus.Open.ResearchFormalization.R0314Claim19694
