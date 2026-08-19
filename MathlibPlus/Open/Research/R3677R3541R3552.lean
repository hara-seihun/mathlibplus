import Mathlib

namespace MathlibPlus.Open.Research.R3677R3541R3552

noncomputable section

def claim47658_noZeroPreservingFamilyLeftInverse : Prop :=
  ∀ {Index X Y : Type*} [Zero X] [Zero Y]
    (P : Index → X → Y) (D : Index → Y → X)
    (mode : Index → X),
    (∃ U : Index, mode U ≠ 0 ∧ P U (mode U) = 0) →
    (∀ U : Index, D U 0 = 0) →
    ¬ (∀ U : Index, ∀ x : X, D U (P U x) = x)

def claim47884_admissible : Prop :=
  (13 : ℤ) > 0 ∧
    (11 : ℤ) > 0 ∧
    (5 : ℤ) * 13 ≥ 11 - 36 ∧
    (13 : ℤ) ≤ 3 * 11 ∧
    (12 : ℤ) ∣ 13 + 11 ∧
    (13 : ℤ) ≤ 2 * 11

def claim47954_admissible : Prop :=
  ((15 : ℤ) + 9) / 12 = 2 ∧
    (15 : ℤ) > 0 ∧
    (9 : ℤ) > 0 ∧
    (5 : ℤ) * 15 ≥ 9 - 36 ∧
    (15 : ℤ) ≤ 3 * 9 ∧
    (12 : ℤ) ∣ 15 + 9 ∧
    (15 : ℤ) ≤ 2 * 9

end

end MathlibPlus.Open.Research.R3677R3541R3552
