import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

noncomputable section
open scoped BigOperators
open Classical

/-! Retained-top Boolean upset elements. -/

structure TSRaw (q : ℕ) where
  T : Finset (Fin q)
  H : Finset (Finset (Fin q))
deriving DecidableEq, Fintype

def IsUpsetOn (T : Finset (Fin q)) (H : Finset (Finset (Fin q))) : Prop :=
  (∀ S ∈ H, S ⊆ T) ∧
    ∀ S ∈ H, ∀ R, S ⊆ R → R ⊆ T → R ∈ H

def TSValid {q : ℕ} (x : TSRaw q) : Prop :=
  x.H.Nonempty ∧ IsUpsetOn x.T x.H

def TS_q (q : ℕ) := {x : TSRaw q // TSValid x}

def retainedTopTSClaim
    (q : ℕ) (T : Finset (Fin q)) (H : Finset (Finset (Fin q))) : Prop :=
  TSValid ⟨T, H⟩

def tsProjection {q : ℕ}
    (V : Finset (Fin q)) (H : Finset (Finset (Fin q))) : Finset (Finset (Fin q)) :=
  H.image (fun S => S ∩ V)

def tsCylinder {q : ℕ}
    (T V : Finset (Fin q)) (H : Finset (Finset (Fin q))) : Finset (Finset (Fin q)) :=
  V.powerset.filter (fun R => R ∩ T ∈ H)

def tsLE {q : ℕ} (x y : TSRaw q) : Prop :=
  x.T ⊆ y.T ∧ tsProjection x.T y.H ⊆ x.H

def tsClosedInterval {q : ℕ} (x y z : TSRaw q) : Prop :=
  tsLE x z ∧ tsLE z y

def tsOrderAndIntervalClaim (q : ℕ) : Prop :=
  (∀ x y : TSRaw q, TSValid x → TSValid y →
    (tsLE x y ↔ x.T ⊆ y.T ∧ tsProjection x.T y.H ⊆ x.H)) ∧
    (∀ x y z : TSRaw q, TSValid x → TSValid y → TSValid z →
      (tsClosedInterval x y z ↔
        x.T ⊆ z.T ∧ z.T ⊆ y.T ∧
          tsProjection z.T y.H ⊆ z.H ∧ z.H ⊆ tsCylinder x.T z.T x.H)) ∧
    (∀ (V : Finset (Fin q)) (H K : Finset (Finset (Fin q))),
      TSValid ⟨V, H⟩ → TSValid ⟨V, K⟩ →
        (tsLE ⟨V, H⟩ ⟨V, K⟩ ↔ K ⊆ H))

/-! Join and meet formulas. -/

def tsJoinRaw {q : ℕ} (x y : TSRaw q) : TSRaw q where
  T := x.T ∪ y.T
  H := tsCylinder x.T (x.T ∪ y.T) x.H ∩
    tsCylinder y.T (x.T ∪ y.T) y.H

def tsMeetRaw {q : ℕ} (x y : TSRaw q) : TSRaw q where
  T := x.T ∩ y.T
  H := tsProjection (x.T ∩ y.T) x.H ∪ tsProjection (x.T ∩ y.T) y.H

def tsLatticeOperationsClaim (q : ℕ) : Prop :=
  ∀ x y : TSRaw q, TSValid x → TSValid y →
    (TSValid (tsJoinRaw x y) ∧ TSValid (tsMeetRaw x y) ∧
      (∀ z : TSRaw q, TSValid z →
        (tsLE (tsJoinRaw x y) z ↔ tsLE x z ∧ tsLE y z)) ∧
      (∀ z : TSRaw q, TSValid z →
        (tsLE z (tsMeetRaw x y) ↔ tsLE z x ∧ tsLE z y)))

/-! Atoms and atomic intervals. -/

def tsMinimalElements {q : ℕ}
    (H : Finset (Finset (Fin q))) : Finset (Finset (Fin q)) :=
  H.filter (fun S => ∀ R ∈ H, R ⊆ S → S ⊆ R)

def tsAtomF {q : ℕ} (x : TSRaw q) (i : Fin q) : TSRaw q where
  T := x.T ∪ {i}
  H := tsCylinder x.T (x.T ∪ {i}) x.H

def tsAtomE {q : ℕ} (x : TSRaw q) (s : Finset (Fin q)) : TSRaw q where
  T := x.T
  H := x.H.erase s

def tsCovers {q : ℕ} (x z : TSRaw q) : Prop :=
  tsLE x z ∧ x ≠ z ∧
    ∀ w : TSRaw q, TSValid w → tsLE x w → tsLE w z → w = x ∨ w = z

def tsAtomFinset {q : ℕ} (x y : TSRaw q) : Finset (TSRaw q) :=
  Finset.univ.filter (fun z => TSValid z ∧ tsCovers x z ∧ tsLE z y)

def tsListedAtoms {q : ℕ} (x y : TSRaw q) : Finset (TSRaw q) :=
  (y.T \ x.T).biUnion (fun i => {tsAtomF x i}) ∪
    (tsMinimalElements x.H \ tsProjection x.T y.H).biUnion
      (fun s => {tsAtomE x s})

def IsJoinOfRaw {q : ℕ}
    (S : Finset (TSRaw q)) (j : TSRaw q) : Prop :=
  TSValid j ∧
    (∀ z ∈ S, TSValid z → tsLE z j) ∧
      ∀ w, TSValid w → (∀ z ∈ S, TSValid z → tsLE z w) → tsLE j w

def tsAtomFormulaClaim (q : ℕ) : Prop :=
  ∀ x y : TSRaw q,
    TSValid x → TSValid y → tsLE x y →
      let A := y.T \ x.T
      let P := tsProjection x.T y.H
      let D := tsMinimalElements x.H \ P
      (tsAtomFinset x y = tsListedAtoms x y ∧
        (tsAtomFinset x y).card = A.card + D.card ∧
        IsJoinOfRaw (tsAtomFinset x y)
          {T := y.T, H := tsCylinder x.T y.T (x.H \ D)})

def tsAtomicInterval {q : ℕ} (x y : TSRaw q) : Prop :=
  tsLE x y ∧ IsJoinOfRaw (tsAtomFinset x y) y

def tsAtomicityCriterionClaim (q : ℕ) : Prop :=
  ∀ x y : TSRaw q, TSValid x → TSValid y → tsLE x y →
    (tsAtomicInterval x y ↔
      y.H = tsCylinder x.T y.T
        (x.H \ (tsMinimalElements x.H \ tsProjection x.T y.H)))

/-! Dedekind numbers and the cardinality formula. -/

def DedekindUpset (r : ℕ) :=
  {H : Finset (Finset (Fin r)) // IsUpsetOn (Finset.univ : Finset (Fin r)) H}

noncomputable instance dedekindUpsetFinite (r : ℕ) : Finite (DedekindUpset r) := by
  apply Finite.of_injective (fun x : DedekindUpset r => x.1)
  exact Subtype.val_injective

noncomputable instance dedekindUpsetFintype (r : ℕ) : Fintype (DedekindUpset r) :=
  Fintype.ofFinite _

def dedekindNumber (r : ℕ) : ℕ :=
  Fintype.card (DedekindUpset r)

def tsCardinalityFormulaClaim (q : ℕ) : Prop :=
  Nat.card (TS_q q) =
    ∑ r ∈ Finset.range (q + 1), Nat.choose q r * (dedekindNumber r - 1)

end
end MathlibPlus.Open.FormalizationBatch
