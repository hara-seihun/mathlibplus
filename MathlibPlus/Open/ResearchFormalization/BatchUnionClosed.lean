import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

noncomputable section

/-- Pairwise union closure for a finite family of finite sets. -/
def pairwiseUnionClosed {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  ∀ ⦃A B : Finset α⦄, A ∈ F → B ∈ F → A ∪ B ∈ F

/-- Separation of the points of a finite ground set by a family. -/
def separatingFamily {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  ∀ ⦃x y : α⦄, x ≠ y →
    ∃ A ∈ F, (x ∈ A) ≠ (y ∈ A)

/-- Frequency of a point in a nonempty finite family. -/
def familyFrequency {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (x : α) : ℚ :=
  (F.filter (fun A => x ∈ A)).card / F.card

/-- The five-member union-closed family from the finite tensorisation failure. -/
def tensorisationWitness : Finset (Finset (Fin 3)) :=
  ({∅, {0}, {0, 1}, {0, 2}, {0, 1, 2}} : Finset (Finset (Fin 3)))

/-- Absence bits for coordinates 1 and 2, in the order used by the packet. -/
def witnessAbsencePattern (A : Finset (Fin 3)) : Fin 2 → Bool :=
  fun i => decide ((if i = 0 then (1 : Fin 3) else 2) ∉ A)

/-- A concrete two-bit pattern, with the first coordinate listed first. -/
def twoBitPattern (b₀ b₁ : Bool) : Fin 2 → Bool :=
  fun i => if i = 0 then b₀ else b₁

def pattern11 : Fin 2 → Bool := twoBitPattern true true
def pattern01 : Fin 2 → Bool := twoBitPattern false true
def pattern10 : Fin 2 → Bool := twoBitPattern true false
def pattern00 : Fin 2 → Bool := twoBitPattern false false

/-- The exact uniform law of a pattern map on a finite family. -/
def uniformPatternLaw
    (F : Finset (Finset (Fin 3)))
    (pattern : Finset (Fin 3) → (Fin 2 → Bool))
    (p : Fin 2 → Bool) : ℚ :=
  (F.filter (fun A => pattern A = p)).card / F.card

/-- Coordinatewise AND of the two absence patterns in a pair of samples. -/
def witnessPairPattern
    (A B : Finset (Fin 3)) : Fin 2 → Bool :=
  fun i => witnessAbsencePattern A i && witnessAbsencePattern B i

/-- The exact uniform law of the two-fold absence-pattern AND. -/
def uniformPairPatternLaw (p : Fin 2 → Bool) : ℚ :=
  ((tensorisationWitness.product tensorisationWitness).filter
      (fun AB => witnessPairPattern AB.1 AB.2 = p)).card /
    (tensorisationWitness.card ^ 2)

/-- Binary relative entropy, with the positive arguments used below. -/
def binaryRelativeEntropy (a b : ℝ) : ℝ :=
  a * (Real.log (a / b) / Real.log 2) +
    (1 - a) * (Real.log ((1 - a) / (1 - b)) / Real.log 2)

/-- The joint two-coordinate divergence displayed in the packet. -/
def witnessJointDivergence : ℝ :=
  (11 / 25 : ℝ) * (Real.log (11 / 5) / Real.log 2) +
    (4 / 25 : ℝ) * (Real.log (2 / 5) / Real.log 2)

/-- The sum of the two singleton lower bounds displayed in the packet. -/
def witnessSingletonSum : ℝ :=
  2 * ((9 / 25 : ℝ) * (Real.log (3 / 5) / Real.log 2) +
    (16 / 25 : ℝ) * (Real.log (8 / 5) / Real.log 2))

/--
The exact finite failure of singleton KL tensorisation: the family, its
frequencies, both finite pattern laws, and the strict divergence comparison
are all retained.
-/
def exactSingletonKLTensorisationFailure : Prop :=
  pairwiseUnionClosed tensorisationWitness ∧
    separatingFamily tensorisationWitness ∧
    familyFrequency tensorisationWitness 0 = (4 / 5 : ℚ) ∧
    familyFrequency tensorisationWitness 1 = (2 / 5 : ℚ) ∧
    familyFrequency tensorisationWitness 2 = (2 / 5 : ℚ) ∧
    uniformPatternLaw tensorisationWitness witnessAbsencePattern pattern11 =
      (2 / 5 : ℚ) ∧
    uniformPatternLaw tensorisationWitness witnessAbsencePattern pattern01 =
      (1 / 5 : ℚ) ∧
    uniformPatternLaw tensorisationWitness witnessAbsencePattern pattern10 =
      (1 / 5 : ℚ) ∧
    uniformPatternLaw tensorisationWitness witnessAbsencePattern pattern00 =
      (1 / 5 : ℚ) ∧
    uniformPairPatternLaw pattern11 = (4 / 25 : ℚ) ∧
    uniformPairPatternLaw pattern01 = (5 / 25 : ℚ) ∧
    uniformPairPatternLaw pattern10 = (5 / 25 : ℚ) ∧
    uniformPairPatternLaw pattern00 = (11 / 25 : ℚ) ∧
    witnessJointDivergence < witnessSingletonSum

end

end MathlibPlus.Open.ResearchFormalizationBatch
