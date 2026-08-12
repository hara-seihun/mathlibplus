import MathlibPlus.Algebra.LinearQuadraticFactorization

namespace MathlibPlus.GraphTheory.Claim50675

/-- The exact weighted combination of the two displayed inequalities. -/
theorem bridgeCombinationIdentity_claim50675 (N L : ℚ) :
    (3 / 4 : ℚ) * (N - L) + L = (3 * N + L) / 4 := by
  ring

/-- The displayed right-hand side is at most `N` under the retained ordering
hypothesis.  The source condition `L≥6` is retained even though the algebraic
bound only uses `L≤N`. -/
theorem bridgeCombinationBound_claim50675 {N L : ℚ}
    (_hL : 6 ≤ L) (hLN : L ≤ N) :
    (3 * N + L) / 4 ≤ N := by
  linarith

/-- All four displayed coefficients are at least three. -/
theorem bridgeCoefficientsAtLeastThree_claim50675 :
    (3 : ℚ) ≤ 3 ∧ (3 : ℚ) ≤ 13 / 4 ∧
      (3 : ℚ) ≤ 7 / 2 ∧ (3 : ℚ) ≤ 3 := by
  norm_num

/-- The integer floor consequence of `3|M|≤N`, with `M` represented by a
nonnegative cardinality. -/
theorem bridgeFloorConsequence_claim50675 {N M : ℕ}
    (hM : 3 * M ≤ N) : M ≤ N / 3 := by
  omega

end MathlibPlus.GraphTheory.Claim50675
