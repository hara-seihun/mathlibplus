import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0527MomentPencil

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

private abbrev CoverPolynomial := MvPolynomial ℕ ℤ

private def connectedWithin {V : Type*} [DecidableEq V]
    (B : SimpleGraph V) (S : Finset V) : Prop :=
  S.Nonempty ∧
    ∀ ⦃v w : V⦄, v ∈ S → w ∈ S →
      Relation.ReflTransGen
        (fun x y : V => B.Adj x y ∧ x ∈ S ∧ y ∈ S) v w

private def uncovered {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (Finset V)) : Finset V :=
  Finset.univ \ C.biUnion (fun S => S)

private def independentSet {V : Type*} [DecidableEq V]
    (B : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃v w : V⦄, v ∈ S → w ∈ S → v ≠ w → ¬ B.Adj v w

private def connectedCover {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (r : V) (C : Finset (Finset V)) : Prop :=
  (∀ S ∈ C, connectedWithin B S) ∧
    (∀ S ∈ C, ∀ T ∈ C, S ≠ T → Disjoint S T) ∧
    (∃ S ∈ C, r ∈ S) ∧
    independentSet B (uncovered C)

private noncomputable def coverPolynomial
    {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (r : V) : CoverPolynomial :=
  ∑ C : Finset (Finset V),
    if connectedCover B r C then
      MvPolynomial.C ((-1 : ℤ) ^ (uncovered C).card) *
        C.prod (fun S => MvPolynomial.X S.card)
    else 0

private def substituteCover
    {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (r : V)
    (weights : ℕ → CoverPolynomial) : CoverPolynomial :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C : ℤ →+* CoverPolynomial) weights (coverPolynomial B r)

private def momentMessage
    {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (r : V)
    (q a : CoverPolynomial) : CoverPolynomial :=
  substituteCover B r (fun s => if s = 1 then q else a)

private def coarseWeight (s : ℕ) : CoverPolynomial :=
  if s = 1 then MvPolynomial.X 0 else MvPolynomial.X 1

private def shiftedWeight (m s : ℕ) : CoverPolynomial :=
  if s = 1 then MvPolynomial.X 0
  else if s = m then MvPolynomial.X (m + 1)
  else MvPolynomial.X 1 + MvPolynomial.X (s + 1)

private def messagePolynomial
    {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (r : V) : CoverPolynomial :=
  ∑ C : Finset (Finset V),
    if connectedCover B r C then
      MvPolynomial.C ((-1 : ℤ) ^ (uncovered C).card) *
        C.prod (fun S => coarseWeight S.card)
    else 0

private def spectralNormalPolynomial
    {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (r : V) (m : ℕ) : CoverPolynomial :=
  ∑ C : Finset (Finset V),
    if connectedCover B r C then
      MvPolynomial.C ((-1 : ℤ) ^ (uncovered C).card) *
        C.prod (fun S => shiftedWeight m S.card)
    else 0

private def wholeCover {V : Type*} [Fintype V] [DecidableEq V] : Finset (Finset V) :=
  {Finset.univ}

private def normalDelta
    {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (r : V) (m : ℕ) : CoverPolynomial :=
  ∑ C : Finset (Finset V),
    if connectedCover B r C ∧ C ≠ wholeCover then
      MvPolynomial.C ((-1 : ℤ) ^ (uncovered C).card) *
        (C.prod (fun S => shiftedWeight m S.card) -
          C.prod (fun S => coarseWeight S.card))
    else 0

private def normalZero (m : ℕ) (P : CoverPolynomial) : CoverPolynomial :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C : ℤ →+* CoverPolynomial)
    (fun i =>
      if i = 0 then MvPolynomial.X 0
      else if i = 1 then MvPolynomial.X 1
      else if i = m + 1 then MvPolynomial.X (m + 1)
      else 0)
    P

/-- Claim 22379: the connected-cover moment pencil gives the diagonal `a^m`. -/
def claim22379 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (r : V) (m : ℕ),
    B.IsTree → Fintype.card V = m →
      ∀ a : CoverPolynomial,
        momentMessage B r a a = a ^ m

/-- Claim 22383: the explicit spectral/normal connected-cover refinement has a
unique pair consisting of the coarse message minus `a` and a zero-normal
remainder. -/
def claim22383 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (r : V) (m : ℕ),
    B.IsTree → Fintype.card V = m → 2 ≤ m →
      ∃! pair : CoverPolynomial × CoverPolynomial,
        pair.1 = messagePolynomial B r - MvPolynomial.X 1 ∧
          pair.2 = normalDelta B r m ∧
          spectralNormalPolynomial B r m =
            MvPolynomial.X (m + 1) + pair.1 + pair.2 ∧
          normalZero m pair.2 = 0

end

end MathlibPlus.Open.NewResearch2.R0527MomentPencil
