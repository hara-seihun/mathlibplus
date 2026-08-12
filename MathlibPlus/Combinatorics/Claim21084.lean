import MathlibPlus.Algebra.LinearQuadraticFactorization

namespace MathlibPlus.Combinatorics.Claim21084

/-- The exact product contradiction in claim 21084. -/
theorem productContradiction_claim21084 {a b : ℚ}
    (ha : 8 ≤ a) (hb : 8 ≤ b) (hs : 22 ≤ a + b) (hab : a * b ≤ 80) :
    False := by
  have hxy : 0 ≤ (a - 8) * (b - 8) := by
    exact mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
  nlinarith

end MathlibPlus.Combinatorics.Claim21084
