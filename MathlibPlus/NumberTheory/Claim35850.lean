import Mathlib

namespace MathlibPlus.NumberTheory.Claim35850

/-- The admissible index interval for the affine-pronic trace in claim 35850. -/
def affinePronicIndexSet (B U N : ℤ) : Set ℤ :=
  {u | 0 ≤ u ∧ u ≤ U ∧ 0 ≤ B + u * (u + 1) ∧ B + u * (u + 1) < N}

/-- The affine-pronic trace of `R` at the shift `B`. -/
def affinePronicTrace (B U N : ℤ) (R : Set ℤ) : Set ℤ :=
  {u | u ∈ affinePronicIndexSet B U N ∧ B + u * (u + 1) ∈ R}

theorem mem_affinePronicTrace_iff (B U N : ℤ) (R : Set ℤ) (u : ℤ) :
    u ∈ affinePronicTrace B U N R ↔
      0 ≤ u ∧ u ≤ U ∧ 0 ≤ B + u * (u + 1) ∧
        B + u * (u + 1) < N ∧ B + u * (u + 1) ∈ R := by
  simp only [affinePronicTrace, Set.mem_setOf_eq, affinePronicIndexSet]
  tauto

end MathlibPlus.NumberTheory.Claim35850
