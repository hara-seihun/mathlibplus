import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0096

noncomputable section

/-- The contiguous rank-`N` minor of the doubly indexed real family `g`. -/
noncomputable def tau_claim17910
    (g : ℕ → ℕ → ℝ) (N a b : ℕ) : ℝ :=
  Matrix.det (fun i j : Fin N =>
    g (a + i.val) (b + j.val))

/-- The two diagonal minors used as the domain condition for the normalized
contiguous correlation. -/
def positiveDiagonalMinors_claim17910
    (g : ℕ → ℕ → ℝ) (N a : ℕ) : Prop :=
  0 < tau_claim17910 g N a a ∧
    0 < tau_claim17910 g N (a + 1) (a + 1)

/-- Claim 17910: on the positive-diagonal domain, the normalized contiguous
correlation is the neighboring minor divided by the square root of the two
positive diagonal minors. -/
noncomputable def normalizedCorrelation_claim17910
    (g : ℕ → ℕ → ℝ) (N a : ℕ)
    (_positive : positiveDiagonalMinors_claim17910 g N a) : ℝ :=
  tau_claim17910 g N (a + 1) a /
    Real.sqrt (tau_claim17910 g N a a *
      tau_claim17910 g N (a + 1) (a + 1))

end
end MathlibPlus.Open.NewResearch2.R0096
