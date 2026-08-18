import MathlibPlus.Open.ResearchFormalization.BatchO0078

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Claim12169CenteredPositiveSplinePrimitive

noncomputable section

open MathlibPlus.Open.ResearchFormalization.BatchO0078

private noncomputable def g6Spline (u : ℝ) : ℝ :=
  (1 / 12 : ℝ) *
    Finset.sum (Finset.Icc 1 (Nat.floor (Real.exp u))) (fun n =>
      (((n : ℝ) / Real.exp u) ^ 2) *
        (1 - ((n : ℝ) / Real.exp u) ^ 2) ^ 4)

private noncomputable def splineConstant : ℝ :=
  32 / 10395

private noncomputable def beta6Spline (u : ℝ) : ℝ :=
  g6Spline u - splineConstant * Real.exp u

private noncomputable def darbouxSpline (u : ℝ) : ℝ :=
  deriv beta6Spline u - beta6Spline u

/-- Claim 12169: the exact fourth-power spline primitive is centered by the
continuum mode `32/10395 · exp u`, has the stated endpoint value, and its
Darboux derivative is the reviewed `h₆` kernel. -/
def claim12169 : Prop :=
  beta6Spline 0 = -splineConstant ∧
    (∀ u : ℝ,
      darbouxSpline u = deriv beta6Spline u - beta6Spline u ∧
      h6 u = darbouxSpline u)

end

end MathlibPlus.Open.ResearchFormalization.Claim12169CenteredPositiveSplinePrimitive
