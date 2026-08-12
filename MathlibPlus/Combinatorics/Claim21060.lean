import MathlibPlus.Algebra.LinearQuadraticFactorization

namespace MathlibPlus.Combinatorics.Claim21060

/-- The exact cardinality consequence of `t≥2N+7` and `|F|=2t+1`. -/
theorem fourNPlus15LowerBound_claim21060 {N t F : ℕ}
    (ht : 2 * N + 7 ≤ t) (hF : F = 2 * t + 1) :
    4 * N + 15 ≤ F := by
  omega

end MathlibPlus.Combinatorics.Claim21060
