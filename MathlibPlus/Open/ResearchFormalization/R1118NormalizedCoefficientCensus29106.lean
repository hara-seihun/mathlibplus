import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1118NormalizedCoefficientCensus29106

abbrev F3 := ZMod 3
abbrev Plane := Fin 2 → F3
abbrev CoefficientTable := Plane → (Fin 3 → F3)

def normalizedCoefficientTable (F : CoefficientTable) : Prop :=
  F 0 = 0

def translationPeriod (F : CoefficientTable) (s : Plane) : Prop :=
  ∀ x : Plane, F (x + s) = F x

def hasNonzeroTranslationPeriod (F : CoefficientTable) : Prop :=
  ∃ s : Plane, s ≠ 0 ∧ translationPeriod F s

noncomputable def affineImageRank (F : CoefficientTable) : ℕ :=
  Module.finrank (ZMod 3)
    (Submodule.span (ZMod 3)
      (Set.range (fun x : Plane => F x - F 0)))

/-- Claim 29106: the normalized coefficient-table carrier is counted exactly,
with the nonzero-period split by affine image rank and the aperiodic residual. -/
def claim29106 : Prop :=
  Nat.card {F : CoefficientTable // normalizedCoefficientTable F} = 3 ^ 24 ∧
    Nat.card {F : CoefficientTable //
      normalizedCoefficientTable F ∧
        hasNonzeroTranslationPeriod F ∧ affineImageRank F = 0} = 1 ∧
      Nat.card {F : CoefficientTable //
        normalizedCoefficientTable F ∧
          hasNonzeroTranslationPeriod F ∧ affineImageRank F = 1} = 416 ∧
        Nat.card {F : CoefficientTable //
          normalizedCoefficientTable F ∧
            hasNonzeroTranslationPeriod F ∧ affineImageRank F = 2} = 2496 ∧
          Nat.card {F : CoefficientTable //
            normalizedCoefficientTable F ∧ hasNonzeroTranslationPeriod F} = 2913 ∧
            Nat.card {F : CoefficientTable //
              normalizedCoefficientTable F ∧ ¬hasNonzeroTranslationPeriod F} =
              3 ^ 24 - 2913 ∧
              3 ^ 24 - 2913 = 282429533568

end MathlibPlus.Open.ResearchFormalization.R1118NormalizedCoefficientCensus29106
