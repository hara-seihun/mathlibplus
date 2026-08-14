import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- The correction set for the abstract two-sided repair lemma. -/
def repairCorrectionSet {A : Type*} [Group A]
    (C P : Subgroup A) (F : A) : Set A :=
  {α | α ∈ P ∧ α * F ∈ C}

/-- The intersection subgroup written as a set, for coset statements. -/
def repairStabilizer {A : Type*} [Group A]
    (C P : Subgroup A) : Set A :=
  {h | h ∈ C ∧ h ∈ P}

/-- A left coset of a set by a specified element. -/
def repairLeftCoset {A : Type*} [Group A]
    (H : Set A) (a : A) : Set A :=
  {x | ∃ h, h ∈ H ∧ x = h * a}

/-- A right coset of the conjugate of a set by a specified element. -/
def repairRightCoset {A : Type*} [Group A]
    (H : Set A) (a : A) : Set A :=
  {x | ∃ h, h ∈ H ∧ x = a * (a⁻¹ * h * a)}

/-- Claim 37174: the abstract repair set is both displayed cosets. -/
def generalTwoSidedRepairTorsor
    {A : Type*} [Group A]
    (C P : Subgroup A) (F : A) : Prop :=
  ∀ (α₀ : P), α₀.1 * F ∈ C →
    Set.Nonempty (repairCorrectionSet C P F) ∧
      repairCorrectionSet C P F = repairLeftCoset (repairStabilizer C P) α₀.1 ∧
      repairCorrectionSet C P F = repairRightCoset (repairStabilizer C P) α₀.1

end MathlibPlus.Open.ResearchFormalization
