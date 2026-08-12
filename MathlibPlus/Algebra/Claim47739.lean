import MathlibPlus.Basic

namespace MathlibPlus.Algebra

/-- Claim R-3529.2: the explicit pair `(K²,c₂)=(11,13)` satisfies all
listed finite arithmetic admissibility conditions. -/
theorem claim47739_exact_admissibility :
    (0 < (11 : ℤ)) ∧
      (0 < (13 : ℤ)) ∧
      (5 * (11 : ℤ) ≥ (13 : ℤ) - 36) ∧
      ((11 : ℤ) ≤ 3 * 13) ∧
      ((12 : ℤ) ∣ 11 + 13) ∧
      ((11 : ℤ) ≤ 2 * 13) := by
  norm_num

end MathlibPlus.Algebra
