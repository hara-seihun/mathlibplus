import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatchR1851

abbrev A11 := ZMod 11
abbrev A11Squared := A11 × A11
abbrev ProjectiveLine11 := Option A11

/-- The slope, with `none` denoting the vertical projective direction. -/
def projectiveDirection11 [Fact (Nat.Prime 11)]
    (v : A11Squared) : ProjectiveLine11 :=
  if v.1 = 0 then none else some (v.2 / v.1)

def projectivelyEquivalent11 (v w : A11Squared) : Prop :=
  ∃ a : A11, a ≠ 0 ∧ w = a • v

def isLineConstantSymmetricFiveColor11
    (c : A11Squared → Fin 5) : Prop :=
  (∀ v, v ≠ (0, 0) → c (-v) = c v) ∧
  (∀ v w, v ≠ (0, 0) → w ≠ (0, 0) →
    projectivelyEquivalent11 v w → c v = c w)

/-- Claim 32905: line-constant symmetric colorings are precisely projective-line profiles. -/
def lineConstantSymmetricFiveColorProfiles11 [Fact (Nat.Prime 11)] : Prop :=
  Fintype.card ProjectiveLine11 = 12 ∧
  ∀ c : A11Squared → Fin 5,
    isLineConstantSymmetricFiveColor11 c ↔
      ∃ profile : ProjectiveLine11 → Fin 5,
        ∀ v, v ≠ (0, 0) → c v = profile (projectiveDirection11 v)

end MathlibPlus.Open.ResearchFormalizationBatchR1851
