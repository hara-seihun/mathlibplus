import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ConeLiftBatch

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

abbrev ConeGround (r : ℕ) (α : Type*) := Sum (Fin (r + 1)) α

def newPoint (r : ℕ) : ConeGround r α := Sum.inl ⟨0, by omega⟩

def paddingPoint (r : ℕ) (i : Fin r) : ConeGround r α :=
  Sum.inl ⟨i.val + 1, by omega⟩

def paddingSet (r : ℕ) : Finset (ConeGround r α) :=
  (Finset.univ : Finset (Fin r)).image (paddingPoint r)

def embedResidual (r : ℕ) (S : Finset α) : Finset (ConeGround r α) :=
  S.image Sum.inr

def conePivot (r : ℕ) : Finset (ConeGround r α) :=
  insert (newPoint r) (paddingSet r)

def coneMember (r : ℕ) (H : Finset α) : Finset (ConeGround r α) :=
  insert (newPoint r) (embedResidual r H)

def coneFamily (r m : ℕ) (H : Fin m → Finset α) :
    Finset (Finset (ConeGround r α)) :=
  insert (conePivot r) ((Finset.univ : Finset (Fin m)).image (coneMember r ∘ H))

def threeSunflower (X Y Z : Finset β) : Prop :=
  X ∩ Y = X ∩ Z ∧ X ∩ Y = Y ∩ Z

def pairwiseIntersecting (F : Finset (Finset β)) : Prop :=
  ∀ X ∈ F, ∀ Y ∈ F, X ≠ Y → (X ∩ Y).Nonempty

def uniformFamily (r : ℕ) (F : Finset (Finset β)) : Prop :=
  ∀ X ∈ F, X.card = r

def threeSunflowerFree (F : Finset (Finset β)) : Prop :=
  ∀ X ∈ F, ∀ Y ∈ F, ∀ Z ∈ F,
    X ≠ Y → X ≠ Z → Y ≠ Z → ¬ threeSunflower X Y Z

def distinctResidualFamily (H : Fin m → Finset α) : Prop :=
  ∀ i j, i ≠ j → H i ≠ H j

def residualHypotheses (r m : ℕ) (H : Fin m → Finset α) : Prop :=
  distinctResidualFamily H ∧
  (∀ i, (H i).card = r) ∧
  pairwiseIntersecting (Finset.univ.image H) ∧
  threeSunflowerFree (Finset.univ.image H)

/-- Claim 36157: the one-trace cone lift and its exact deletion inverse. -/
def exactOneTraceConeLift : Prop :=
  ∀ {α : Type*} [DecidableEq α] (r m : ℕ) (H : Fin m → Finset α),
    residualHypotheses r m H →
      let A := conePivot (α := α) r
      let F := coneFamily (α := α) r m H
      uniformFamily (r + 1) F ∧
      pairwiseIntersecting F ∧
      threeSunflowerFree F ∧
      (∀ i : Fin m,
        A ∩ coneMember r (H i) = {newPoint r} ∧
        coneMember r (H i) \ A = embedResidual r (H i)) ∧
      A ∈ F

/-- Claim 36158: the sunflower test on three residual members is unchanged. -/
def coneLiftThreeSunflowerFree : Prop :=
  ∀ {α : Type*} [DecidableEq α] (r m : ℕ) (H : Fin m → Finset α),
    residualHypotheses r m H →
      (∀ i j k : Fin m,
        i ≠ j → i ≠ k → j ≠ k →
        (threeSunflower (coneMember r (H i))
          (coneMember r (H j)) (coneMember r (H k)) ↔
         threeSunflower (H i) (H j) (H k))) ∧
      (∀ i j : Fin m, i ≠ j → (H i ∩ H j).Nonempty →
        ¬ threeSunflower (conePivot (α := α) r)
          (coneMember r (H i)) (coneMember r (H j)))

def positiveSingletonResidualIncidence (r m : ℕ) (H : Fin m → Finset α) : Prop :=
  ∃ i : Fin m, (H i).Nonempty

def nonSingletonPivotTrace (r m : ℕ) (H : Fin m → Finset α) : Prop :=
  ∃ X ∈ coneFamily r m H, X ≠ conePivot (α := α) r ∧
    2 ≤ ((conePivot (α := α) r) ∩ X).card

/-- Claim 36159: the cone is a counterexample to every proposed positive
medium-singleton charge whose target is a non-singleton pivot trace. -/
def noUniversalCrossLevelCharge : Prop :=
  ∀ {α : Type*} [DecidableEq α] (r m : ℕ) (H : Fin m → Finset α),
    residualHypotheses r m H → positiveSingletonResidualIncidence r m H →
      (∀ X ∈ coneFamily r m H, X ≠ conePivot (α := α) r →
        ((conePivot (α := α) r) ∩ X).card = 1) ∧
      ¬ (positiveSingletonResidualIncidence r m H →
        nonSingletonPivotTrace r m H)

def allTSubsets (m t : ℕ) : Finset (Finset (Fin m)) :=
  (Finset.univ : Finset (Finset (Fin m))).filter (fun S => S.card = t)

def balancedResidualMember (m t : ℕ) (i : Fin m) :
    Finset (Finset (Fin m)) :=
  (allTSubsets m t).filter (fun S => i ∈ S)

def balancedResidualFamily (m t : ℕ) :
    Fin m → Finset (Finset (Fin m)) := balancedResidualMember m t

def balancedCoordinateDegree (m t : ℕ) (S : Finset (Fin m)) : ℕ :=
  ((Finset.univ : Finset (Fin m)).filter
    (fun i => S ∈ balancedResidualMember m t i)).card

/-- Claim 36160. -/
def balancedMediumDegreeSpecialization : Prop :=
  ∀ (m t : ℕ), 4 ≤ m → 2 ≤ t → t ≤ m - 1 →
    let H := balancedResidualFamily m t
    (∀ i : Fin m, (H i).card = Nat.choose (m - 1) (t - 1)) ∧
    (∀ S ∈ allTSubsets m t, balancedCoordinateDegree m t S = t) ∧
    pairwiseIntersecting (Finset.univ.image H) ∧
    threeSunflowerFree (Finset.univ.image H) ∧
    residualHypotheses (Nat.choose (m - 1) (t - 1)) m H ∧
    uniformFamily (Nat.choose (m - 1) (t - 1) + 1)
      (coneFamily (α := Finset (Fin m))
        (Nat.choose (m - 1) (t - 1)) m H) ∧
    ((t = m / 2) →
      ((Finset.univ : Finset (Finset (Fin m))).filter
        (fun S => S.card = t)).card = Nat.choose m t)

/-- Claim 36162: adjoining the actual pivot and deleting it are explicit
mutually inverse operations on the residual support. -/
def exactConeMethodMechanism : Prop :=
  ∀ {α : Type*} [DecidableEq α] (r m : ℕ) (H : Fin m → Finset α),
    residualHypotheses r m H →
      (∀ i : Fin m,
        (coneMember r (H i)) \ conePivot (α := α) r = embedResidual r (H i)) ∧
      (∀ X ∈ coneFamily r m H, X = conePivot (α := α) r ∨
        ∃ i : Fin m, X = coneMember r (H i))

/-- Claim 36163: the finite replay is stated as a finite restriction of the
same exact cone construction, not as a replacement for its all-order form. -/
def finiteConeReplayEvidence : Prop :=
  (∀ {α : Type*} [Fintype α] [DecidableEq α], Fintype.card α ≤ 5 →
    ∀ (r m : ℕ) (H : Fin m → Finset α), residualHypotheses r m H →
      uniformFamily (r + 1) (coneFamily r m H) ∧
      pairwiseIntersecting (coneFamily r m H) ∧
      threeSunflowerFree (coneFamily r m H)) ∧
  (∀ (m t : ℕ), 4 ≤ m → m ≤ 10 → 2 ≤ t → t ≤ m - 1 →
    residualHypotheses (Nat.choose (m - 1) (t - 1)) m
      (balancedResidualFamily m t))

end MathlibPlus.Open.ConeLiftBatch
