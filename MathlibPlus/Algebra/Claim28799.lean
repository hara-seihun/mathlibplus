import MathlibPlus.Algebra.LinearQuadraticFactorization

namespace MathlibPlus.Algebra.Claim28799

/-- The exact normalized-map arithmetic and corrected total from claim 28799. -/
theorem normalizedMapCounts_claim28799 :
    (1 + 11 * 19 + Nat.choose 11 2 * 19 ^ 2 = 20_065) ∧
      (1 + 11 * 41 + Nat.choose 11 2 * 41 ^ 2 = 92_907) ∧
      (20_065 + 92_907 = 112_972) ∧
      (115_832 - 112_972 = 880 + 1_980) := by
  norm_num [Nat.choose]

end MathlibPlus.Algebra.Claim28799
