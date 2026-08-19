import MathlibPlus.Open.ResearchFormalizationBatch20463

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalization.R0365.Claim20464

noncomputable section

open MathlibPlus.Open.ResearchFormalizationBatch20463

/-- The coefficient of the coordinate at common-neighbor count `c` in the
ordered degree-refined deletion recurrence. -/
def targetCoefficient (n : ℕ) (ε : Bool) (d e c : ℕ) : ℤ :=
  (n : ℤ) - 2 - (d : ℤ) - (e : ℤ) +
    2 * adjacencyBit ε + (c : ℤ)

/-- The total of one ordered joint-degree block.  The range contains every
possible common-neighbor count for a finite simple graph. -/
def jointDegreeBlockTotal {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ε : Bool) (d e : ℕ) : ℕ :=
  ∑ c ∈ Finset.range (Fintype.card V + 1), pairProfile G ε d e c

/-- The exact integer equation solved for a positive-coefficient coordinate
when the higher `d+e` coordinates are already available. -/
def positiveRecoveryEquation {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ε : Bool) (d e c : ℕ) (z : ℤ) : Prop :=
  targetCoefficient (Fintype.card V) ε d e c * z =
    (deletedPairProfileSum G ε d e c : ℤ) -
      (((d : ℤ) + 1 - adjacencyBit ε - (c : ℤ)) *
        (pairProfile G ε (d + 1) e c : ℤ)) -
      (((e : ℤ) + 1 - adjacencyBit ε - (c : ℤ)) *
        (pairProfile G ε d (e + 1) c : ℤ)) -
      (((c : ℤ) + 1) *
        (pairProfile G ε (d + 1) (e + 1) (c + 1) : ℤ))

/-- Every positive-coefficient coordinate is the unique solution of the
recorded deletion equation, so it is recovered in descending `d+e`. -/
def descendingPositiveRecovery {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ε : Bool) (d e : ℕ) : Prop :=
  ∀ c : ℕ, 0 < targetCoefficient (Fintype.card V) ε d e c →
    positiveRecoveryEquation G ε d e c
        (pairProfile G ε d e c : ℤ) ∧
      ∃! z : ℤ, positiveRecoveryEquation G ε d e c z

/-- At the zero coefficient, the remaining coordinate is the block total
minus the already recovered positive-coefficient coordinates. -/
def boundaryCoordinateRecovery {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ε : Bool) (d e : ℕ) : Prop :=
  ∀ c : ℕ, targetCoefficient (Fintype.card V) ε d e c = 0 →
    (pairProfile G ε d e c : ℤ) =
      (jointDegreeBlockTotal G ε d e : ℤ) -
        Finset.sum
          ((Finset.range (Fintype.card V + 1)).filter
            (fun c' => 0 < targetCoefficient (Fintype.card V) ε d e c'))
          (fun c' => (pairProfile G ε d e c' : ℤ))

/-- Claim 20464: the affine coefficient has one possible zero coordinate in
an ordered joint-degree block, positive coordinates are recovered by the
ascending-coordinate terms of the exact card recurrence in descending `d+e`,
and the unique boundary coordinate is recovered from the block total. -/def claim20464_oneBoundaryCoordinatePerJointDegreeBlock : Prop :=
  (∀ (n : ℕ) (ε : Bool) (d e : ℕ),
    (∀ c : ℕ,
      targetCoefficient n ε d e c = 0 ↔
        (c : ℤ) = (d : ℤ) + (e : ℤ) -
          2 * adjacencyBit ε - ((n : ℤ) - 2)) ∧
    (∀ c₁ c₂ : ℕ,
      targetCoefficient n ε d e c₁ = 0 →
      targetCoefficient n ε d e c₂ = 0 →
      c₁ = c₂)) ∧
  (∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ε : Bool) (d e : ℕ),
    descendingPositiveRecovery G ε d e ∧
      boundaryCoordinateRecovery G ε d e)

end

end MathlibPlus.Open.ResearchFormalization.R0365.Claim20464
