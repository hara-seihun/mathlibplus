import MathlibPlus.Open.ResearchFormalization.R0162Claim18460

namespace MathlibPlus.Open.ResearchFormalization.R0162Claim18454

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R0162Claim18460

/-- Claim 18454: with `W[A,C]=AC'-A'C`, the quotient Wronskian is
`A^2 J'` wherever the displayed quotient is differentiable. -/
def claim18454 : Prop :=
  ∀ (H E : ℝ → ℝ) (t A' C' J' : ℝ),
    relativeA H t ≠ 0 →
      HasDerivAt (relativeA H) A' t →
        HasDerivAt (relativeC E) C' t →
          HasDerivAt (relativeQuotient H E) J' t →
            relativeWronskian (relativeA H) (relativeC E) t =
              relativeA H t ^ 2 * J'

end
end MathlibPlus.Open.ResearchFormalization.R0162Claim18454
