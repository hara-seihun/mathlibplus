import Mathlib

namespace MathlibPlus.Open.Research.FormalizationR0314.StateZeroInjectivity19703

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
  ∑ t : Fin (m + 1), interactionOnSym2 (Sym2.mk s t) * message m T r t

private def rootedGraphIso {V W : Type*}
    (T : SimpleGraph V) (r : V) (U : SimpleGraph W) (s : W) : Prop :=
  ∃ e : T ≃g U, e.toEquiv r = s

def stateZeroPinnedFactorInjective19703 : Prop :=
  ∀ (m : ℕ), 1 ≤ m →
    ∀ {V W : Type*} [Fintype V] [DecidableEq V]
      [Fintype W] [DecidableEq W]
      (T : SimpleGraph V) (r : V) (U : SimpleGraph W) (s : W),
      T.IsTree →
      U.IsTree →
      pinnedFactor m T r 0 = pinnedFactor m U s 0 →
        rootedGraphIso T r U s

end

end MathlibPlus.Open.Research.FormalizationR0314.StateZeroInjectivity19703
