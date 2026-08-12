import Mathlib

namespace MathlibPlus.Algebra.Claim16989

/-- Numerical admissibility predicate for the integer Chern-pair data. -/
def numericallyAdmissible (Ksq c₂ : ℤ) : Prop :=
  Ksq > 0 ∧
    c₂ > 0 ∧
    12 ∣ Ksq + c₂ ∧
    5 * Ksq ≥ c₂ - 36 ∧
    Ksq ≤ 3 * c₂

theorem numericallyAdmissible_formula (Ksq c₂ : ℤ) :
    numericallyAdmissible Ksq c₂ ↔
      Ksq > 0 ∧
        c₂ > 0 ∧
        12 ∣ Ksq + c₂ ∧
        5 * Ksq ≥ c₂ - 36 ∧
        Ksq ≤ 3 * c₂ := by
  rfl

end MathlibPlus.Algebra.Claim16989
