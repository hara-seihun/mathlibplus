import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1853.TrainReduction

open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev TrainPlane := Fin 2 → ℝ
abbrev TrainVertex := Fin 3 × Fin 3
abbrev TrainPair := {e : TrainVertex × TrainVertex // e.1 < e.2}
abbrev TrainFlexParameter := Fin 4 → ℝ
abbrev TrainVelocity := TrainVertex → TrainPlane

def trainRotationJ (w : TrainPlane) : TrainPlane :=
  fun i => if i = 0 then -w 1 else w 0

def trainUPosition (u₁ u₂ : TrainPlane) (i : Fin 3) : TrainPlane :=
  if i = 0 then 0 else if i = 1 then u₁ else u₁ + u₂

def trainVPosition (v₁ v₂ : TrainPlane) (j : Fin 3) : TrainPlane :=
  if j = 0 then 0 else if j = 1 then v₁ else v₁ + v₂

def trainPoint (u₁ u₂ v₁ v₂ : TrainPlane)
    (x : TrainVertex) : TrainPlane :=
  trainUPosition u₁ u₂ x.1 + trainVPosition v₁ v₂ x.2

def trainGridPair (e : TrainVertex × TrainVertex) : Prop :=
  (e.1.1 = e.2.1 ∧
      (e.1.2.val + 1 = e.2.2.val ∨ e.2.2.val + 1 = e.1.2.val)) ∨
    (e.1.2 = e.2.2 ∧
      (e.1.1.val + 1 = e.2.1.val ∨ e.2.1.val + 1 = e.1.1.val))

noncomputable def trainGridPairs : Finset TrainPair :=
  (Finset.univ : Finset TrainPair).filter (fun e => trainGridPair e.1)

def trainDistanceSquared (u₁ u₂ v₁ v₂ : TrainPlane)
    (e : TrainPair) : ℝ :=
  ∑ k : Fin 2,
    (trainPoint u₁ u₂ v₁ v₂ e.1.1 k -
      trainPoint u₁ u₂ v₁ v₂ e.1.2 k) ^ 2

def trainPairSquaredDistance (X : TrainVertex → TrainPlane)
    (e : TrainPair) : ℝ :=
  ∑ k : Fin 2, (X e.1.1 k - X e.1.2 k) ^ 2

def trainPairMaximum (X : TrainVertex → TrainPlane) : ℝ :=
  if h : (Finset.univ : Finset TrainPair).Nonempty then
    (Finset.univ : Finset TrainPair).sup' h (trainPairSquaredDistance X)
  else 0

def trainPairMinimum (X : TrainVertex → TrainPlane) : ℝ :=
  if h : (Finset.univ : Finset TrainPair).Nonempty then
    (Finset.univ : Finset TrainPair).inf' h (trainPairSquaredDistance X)
  else 0

def trainPhiOfConfig (X : TrainVertex → TrainPlane) : ℝ :=
  Real.log (trainPairMaximum X) - Real.log (trainPairMinimum X)

def trainPhi (u₁ u₂ v₁ v₂ : TrainPlane) : ℝ :=
  trainPhiOfConfig (trainPoint u₁ u₂ v₁ v₂)

def trainConfigDistance (X Y : TrainVertex → TrainPlane) : ℝ :=
  Real.sqrt (∑ x : TrainVertex, ∑ k : Fin 2, (X x k - Y x k) ^ 2)

def trainLocalMinimum (u₁ u₂ v₁ v₂ : TrainPlane) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ Y : TrainVertex → TrainPlane,
      trainConfigDistance (trainPoint u₁ u₂ v₁ v₂) Y < ε →
        trainPhiOfConfig (trainPoint u₁ u₂ v₁ v₂) ≤ trainPhiOfConfig Y

def nongridStrictSeparation (u₁ u₂ v₁ v₂ : TrainPlane) : Prop :=
  ∀ e : TrainPair, e ∉ trainGridPairs →
    1 < trainDistanceSquared u₁ u₂ v₁ v₂ e

def trainGridTriangleFree : Prop :=
  ∀ a b c : TrainVertex,
    a ≠ b → a ≠ c → b ≠ c →
      ¬ (trainGridPair (a, b) ∧
        trainGridPair (b, c) ∧ trainGridPair (a, c))

def trainUnitTracks (u₁ u₂ v₁ v₂ : TrainPlane) : Prop :=
  (∑ k : Fin 2, u₁ k ^ 2 = 1) ∧
    (∑ k : Fin 2, u₂ k ^ 2 = 1) ∧
      (∑ k : Fin 2, v₁ k ^ 2 = 1) ∧
        (∑ k : Fin 2, v₂ k ^ 2 = 1)

def trainUnitGraphExact (u₁ u₂ v₁ v₂ : TrainPlane) : Prop :=
  (∀ e : TrainPair,
    trainDistanceSquared u₁ u₂ v₁ v₂ e = 1 ↔ e ∈ trainGridPairs) ∧
    trainGridTriangleFree

def trainAngularUVelocity (u₁ u₂ : TrainPlane)
    (z : TrainFlexParameter) (i : Fin 3) : TrainPlane :=
  if i = 0 then 0
  else if i = 1 then z 0 • trainRotationJ u₁
  else z 0 • trainRotationJ u₁ + z 1 • trainRotationJ u₂

def trainAngularVVelocity (v₁ v₂ : TrainPlane)
    (z : TrainFlexParameter) (j : Fin 3) : TrainPlane :=
  if j = 0 then 0
  else if j = 1 then z 2 • trainRotationJ v₁
  else z 2 • trainRotationJ v₁ + z 3 • trainRotationJ v₂

def trainPointVelocity (u₁ u₂ v₁ v₂ : TrainPlane)
    (z : TrainFlexParameter) (x : TrainVertex) : TrainPlane :=
  trainAngularUVelocity u₁ u₂ z x.1 +
    trainAngularVVelocity v₁ v₂ z x.2

def trainDiameterPairs (u₁ u₂ v₁ v₂ : TrainPlane) : Finset TrainPair :=
  (Finset.univ : Finset TrainPair).filter (fun e =>
    ∀ f : TrainPair,
      trainDistanceSquared u₁ u₂ v₁ v₂ f ≤
        trainDistanceSquared u₁ u₂ v₁ v₂ e)

def trainDiameterRow (u₁ u₂ v₁ v₂ : TrainPlane)
    (e : TrainPair) (z : TrainFlexParameter) : ℝ :=
  2 * ∑ k : Fin 2,
    (trainPoint u₁ u₂ v₁ v₂ e.1.1 k -
      trainPoint u₁ u₂ v₁ v₂ e.1.2 k) *
      (trainPointVelocity u₁ u₂ v₁ v₂ z e.1.1 k -
        trainPointVelocity u₁ u₂ v₁ v₂ z e.1.2 k)

def trainBasisFlex (r : Fin 4) : TrainFlexParameter :=
  fun s => if s = r then 1 else 0

def trainDiameterRowVector (u₁ u₂ v₁ v₂ : TrainPlane)
    (e : TrainPair) : TrainFlexParameter :=
  fun r => trainDiameterRow u₁ u₂ v₁ v₂ e (trainBasisFlex r)

def trainRigidRotationParameter : TrainFlexParameter :=
  fun _ => 1

def trainRigidRotationSubspace : Submodule ℝ TrainFlexParameter :=
  Submodule.span ℝ ({trainRigidRotationParameter} : Set TrainFlexParameter)

def trainDiameterRowsRotationInvariant (u₁ u₂ v₁ v₂ : TrainPlane) : Prop :=
  ∀ e : TrainPair,
    trainDiameterRow u₁ u₂ v₁ v₂ e trainRigidRotationParameter = 0

def trainDiameterRowsPositivelySpan (u₁ u₂ v₁ v₂ : TrainPlane) : Prop :=
  ∀ z : TrainFlexParameter,
    (∀ e ∈ trainDiameterPairs u₁ u₂ v₁ v₂,
      0 ≤ trainDiameterRow u₁ u₂ v₁ v₂ e z) →
    z ∈ trainRigidRotationSubspace

def trainDiameterRowsRankThree (u₁ u₂ v₁ v₂ : TrainPlane)
    (D : Finset TrainPair) : Prop :=
  Module.finrank ℝ
    (Submodule.span ℝ
      (Set.range (fun e : {e // e ∈ D} =>
        trainDiameterRowVector u₁ u₂ v₁ v₂ e.1))) = 3

def trainPositiveDiameterCircuit (u₁ u₂ v₁ v₂ : TrainPlane)
    (D : Finset TrainPair) : Prop :=
  D.card = 4 ∧
    D ⊆ trainDiameterPairs u₁ u₂ v₁ v₂ ∧
      trainDiameterRowsRankThree u₁ u₂ v₁ v₂ D ∧
      ∃ w : TrainPair → ℝ,
        (∀ e ∈ D, 0 < w e) ∧
          (∑ e ∈ D, w e = 1) ∧
            (∀ r : Fin 4,
              ∑ e ∈ D,
                w e * trainDiameterRowVector u₁ u₂ v₁ v₂ e r = 0)

def trainFirstOrderIsolated (u₁ u₂ v₁ v₂ : TrainPlane) : Prop :=
  trainLocalMinimum u₁ u₂ v₁ v₂ ∧
    trainDiameterRowsPositivelySpan u₁ u₂ v₁ v₂

def reductionContactRow (u₁ u₂ v₁ v₂ : TrainPlane)
    (e : TrainPair) (W : TrainVelocity) : ℝ :=
  2 * ∑ k : Fin 2,
    (trainPoint u₁ u₂ v₁ v₂ e.1.1 k -
      trainPoint u₁ u₂ v₁ v₂ e.1.2 k) *
      (W e.1.1 k - W e.1.2 k)

def reductionContactFlex (u₁ u₂ v₁ v₂ : TrainPlane)
    (W : TrainVelocity) : Prop :=
  ∀ e ∈ trainGridPairs,
    reductionContactRow u₁ u₂ v₁ v₂ e W = 0

def reductionContactFlexRepresentation
    (u₁ u₂ v₁ v₂ : TrainPlane) : Prop :=
  ∀ W : TrainVelocity, reductionContactFlex u₁ u₂ v₁ v₂ W →
    ∃ t : TrainPlane, ∃ z : TrainFlexParameter,
      ∀ x : TrainVertex,
        W x = t + trainPointVelocity u₁ u₂ v₁ v₂ z x

def reductionContactRowsIndependent
    (u₁ u₂ v₁ v₂ : TrainPlane) : Prop :=
  LinearIndependent ℝ
    (fun e : {e // e ∈ trainGridPairs} =>
      reductionContactRow u₁ u₂ v₁ v₂ e.1)

def reductionRigidRotationSubspace :
    Submodule ℝ TrainFlexParameter :=
  Submodule.span ℝ ({trainRigidRotationParameter} : Set TrainFlexParameter)

def reductionTrainFlexQuotientDimension : Prop :=
  Module.finrank ℝ
    (TrainFlexParameter ⧸ reductionRigidRotationSubspace) = 3

def reductionCenterVertex : TrainVertex := (1, 1)

def reductionBoundaryVertex (x : TrainVertex) : Prop :=
  x ≠ reductionCenterVertex

noncomputable def reductionBoundaryNongridPairs : Finset TrainPair :=
  (Finset.univ : Finset TrainPair).filter (fun e =>
    e ∉ trainGridPairs ∧ reductionBoundaryVertex e.1.1 ∧
      reductionBoundaryVertex e.1.2)

def reductionSameUnorderedPair (g : Equiv.Perm TrainVertex)
    (e f : TrainPair) : Prop :=
  (g e.1.1 = f.1.1 ∧ g e.1.2 = f.1.2) ∨
    (g e.1.1 = f.1.2 ∧ g e.1.2 = f.1.1)

def reductionGridDihedralSymmetry (g : Equiv.Perm TrainVertex) : Prop :=
  ∀ e : TrainPair,
    trainGridPair e.1 ↔ trainGridPair (g e.1.1, g e.1.2)

def reductionSameDihedralSupport (A B : Finset TrainPair) : Prop :=
  ∃ g : Equiv.Perm TrainVertex,
    reductionGridDihedralSymmetry g ∧
      ∀ e : TrainPair, e ∈ B ↔
        ∃ f ∈ A, reductionSameUnorderedPair g f e

def reductionOrbitCensus655 : Prop :=
  ∃ reps : Fin 655 → Finset TrainPair,
    (∀ i, (reps i).card = 4 ∧
      reps i ⊆ reductionBoundaryNongridPairs) ∧
    (∀ A : Finset TrainPair,
      A.card = 4 → A ⊆ reductionBoundaryNongridPairs →
        ∃! i : Fin 655, reductionSameDihedralSupport A (reps i)) ∧
    (∀ i j : Fin 655, i ≠ j →
      ¬ reductionSameDihedralSupport (reps i) (reps j))

/-- Claim 33752: the exact reduction uses the angular track-flex carrier,
its three-dimensional common-rotation quotient, independent contact rows in
the full velocity dual, boundary endpoint reduction, and the 655 dihedral
orbits of four-element boundary supports. -/
def exactTwoByTwoCircuitReduction_claim33752 : Prop :=
  ∀ (u₁ u₂ v₁ v₂ : TrainPlane),
    trainUnitTracks u₁ u₂ v₁ v₂ →
      nongridStrictSeparation u₁ u₂ v₁ v₂ →
        trainUnitGraphExact u₁ u₂ v₁ v₂ ∧
          trainGridPairs.card = 12 ∧
          reductionContactFlexRepresentation u₁ u₂ v₁ v₂ ∧
          reductionContactRowsIndependent u₁ u₂ v₁ v₂ ∧
          reductionTrainFlexQuotientDimension ∧
          trainDiameterRowsRotationInvariant u₁ u₂ v₁ v₂ ∧
          (∀ e ∈ trainDiameterPairs u₁ u₂ v₁ v₂,
            e.1.1 ≠ reductionCenterVertex ∧
              e.1.2 ≠ reductionCenterVertex) ∧
          reductionBoundaryNongridPairs.card = 20 ∧
          reductionOrbitCensus655 ∧
          (trainFirstOrderIsolated u₁ u₂ v₁ v₂ →
            ∃ D : Finset TrainPair,
              trainPositiveDiameterCircuit u₁ u₂ v₁ v₂ D)

end
end MathlibPlus.Open.ResearchFormalization.R1853.TrainReduction
