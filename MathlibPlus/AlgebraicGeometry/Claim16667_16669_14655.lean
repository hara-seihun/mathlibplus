import Mathlib.Tactic.NormNum

namespace MathlibPlus.AlgebraicGeometry

/-- Claim 16667: the exact necessary numerical tests and Noether arithmetic for
`(c₁²,c₂) = (14,10)`.  The declaration records the arithmetic content only;
the source does not provide a Lean surface interface for a geometric
realization. -/
theorem numericalGeography_14_10_claim16667 :
    (14 : ℤ) > 0 ∧
      (10 : ℤ) > 0 ∧
      (5 : ℤ) * 14 ≥ 10 - 36 ∧
      (14 : ℤ) ≤ 3 * 10 ∧
      (12 : ℤ) ∣ 14 + 10 ∧
      ((14 : ℚ) + 10) / 12 = 2 := by
  norm_num

/-- Claim 16669: the exact necessary numerical tests and Noether arithmetic for
`(c₁²,c₂) = (15,9)`.  As in claim 16667, only the displayed arithmetic is
formalized because no surface object is supplied by the source. -/
theorem numericalGeography_15_9_claim16669 :
    (15 : ℤ) > 0 ∧
      (9 : ℤ) > 0 ∧
      (5 : ℤ) * 15 ≥ 9 - 36 ∧
      (15 : ℤ) ≤ 3 * 9 ∧
      (12 : ℤ) ∣ 15 + 9 ∧
      ((15 : ℚ) + 9) / 12 = 2 := by
  norm_num

/-- Claim 14655: the displayed numerical Noether inequality. -/
theorem noetherInequality_claim14655 :
    (5 : ℤ) * 6 ≥ 18 - 36 := by
  norm_num

end MathlibPlus.AlgebraicGeometry
