import Mathlib

namespace MathlibPlus.Open.Research.FormalizationR0314.StateRelabeling19699

noncomputable section

open Classical
open scoped BigOperators

private abbrev PottsPoly (m : ℕ) :=
  MvPolynomial (Fin m ⊕ (Fin m ⊕ Unit)) ℤ

private abbrev PottsRat (m : ℕ) :=
  FractionRing (PottsPoly m)

private def xVariable {m : ℕ} (i : Fin m) : PottsPoly m :=
  MvPolynomial.X (Sum.inl i)

private def zVariable {m : ℕ} (i : Fin m) : PottsPoly m :=
  MvPolynomial.X (Sum.inr (Sum.inl i))

private def yVariable {m : ℕ} : PottsPoly m :=
  MvPolynomial.X (Sum.inr (Sum.inr Unit.unit))

private def baseX {m : ℕ} (i : Fin m) : PottsRat m :=
  algebraMap (PottsPoly m) (PottsRat m) (xVariable i)

private def baseZ {m : ℕ} (i : Fin m) : PottsRat m :=
  algebraMap (PottsPoly m) (PottsRat m) (zVariable i)

private def baseY {m : ℕ} : PottsRat m :=
  algebraMap (PottsPoly m) (PottsRat m) yVariable

private def positiveIndex {m : ℕ}
    (s : Fin (m + 1)) (hs : s ≠ 0) : Fin m :=
  Fin.pred s hs

private def stateInteraction {m : ℕ}
    (y : PottsRat m) (z : Fin m → PottsRat m)
    (e : Sym2 (Fin (m + 1))) : PottsRat m :=
  if e = Sym2.mk 0 0 then 1
  else if h : ∃ i : Fin m, e = Sym2.mk (Fin.succ i) (Fin.succ i) then
    z (Classical.choose h)
  else y

private def edgeInteraction {V : Type*} [Fintype V] [DecidableEq V]
    {m : ℕ} (y : PottsRat m) (z : Fin m → PottsRat m)
    (σ : V → Fin (m + 1)) (e : Sym2 V) : PottsRat m :=
  stateInteraction y z (Sym2.map σ e)

private def edgePairs {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : Finset (Sym2 V) :=
  T.edgeSet.toFinite.toFinset

private def assignmentWeight {V : Type*} [Fintype V] [DecidableEq V]
    {m : ℕ} (x : Fin m → PottsRat m) (y : PottsRat m)
    (z : Fin m → PottsRat m) (T : SimpleGraph V)
    (σ : V → Fin (m + 1)) : PottsRat m :=
  (∏ v : V, if h : σ v = 0 then 1 else x (Fin.pred (σ v) h)) *
    (∏ e ∈ edgePairs T, edgeInteraction y z σ e)

private def message {V : Type*} [Fintype V] [DecidableEq V]
    (m : ℕ) (x : Fin m → PottsRat m) (y : PottsRat m)
    (z : Fin m → PottsRat m) (T : SimpleGraph V) (r : V)
    (s : Fin (m + 1)) : PottsRat m :=
  ∑ σ : V → Fin (m + 1),
    if σ r = s then assignmentWeight x y z T σ else 0

private def pinnedFactor {V : Type*} [Fintype V] [DecidableEq V]
    (m : ℕ) (x : Fin m → PottsRat m) (y : PottsRat m)
    (z : Fin m → PottsRat m) (T : SimpleGraph V) (r : V)
    (s : Fin (m + 1)) : PottsRat m :=
  ∑ t : Fin (m + 1),
    stateInteraction y z (Sym2.mk s t) * message m x y z T r t

private def primedX {m : ℕ}
    (s : Fin (m + 1)) (hs : s ≠ 0) (i : Fin m) : PottsRat m :=
  if i = positiveIndex s hs then
    (baseX i)⁻¹
  else
    baseX i / baseX (positiveIndex s hs)

private def primedZ {m : ℕ}
    (s : Fin (m + 1)) (hs : s ≠ 0) (i : Fin m) : PottsRat m :=
  if i = positiveIndex s hs then
    (baseZ i)⁻¹
  else
    baseZ i / baseZ (positiveIndex s hs)

def exactStateRelabelingReciprocity19699 : Prop :=
  ∀ (m : ℕ), 1 ≤ m →
    ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (T : SimpleGraph V) (r : V),
      T.IsTree →
      ∀ (s : Fin (m + 1)) (hs : s ≠ 0),
        pinnedFactor m baseX baseY baseZ T r s =
          baseX (positiveIndex s hs) ^ Fintype.card V *
            baseZ (positiveIndex s hs) ^ Fintype.card V *
            pinnedFactor m (primedX s hs) (baseY / baseZ (positiveIndex s hs))
              (primedZ s hs) T r 0

end

end MathlibPlus.Open.Research.FormalizationR0314.StateRelabeling19699
