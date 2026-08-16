import MathlibPlus.Open.Analysis.CompletedThetaShellConstruction

namespace MathlibPlus.Open.Analysis.CompletedThetaCenterGapClaim15149

noncomputable section

/-- Claim 15149.  The completed-xi second-derivative quotient has the
certified center-gap enclosure retaining every displayed decimal digit. -/
def completedThetaCenterGapClaim15149 : Prop :=
  let xi : ℂ → ℂ := MathlibPlus.Analysis.ReciprocalXi.xi
  let ell₀ : ℝ :=
    (iteratedDeriv 2 xi (1 / 2 : ℂ) / xi (1 / 2 : ℂ)).re
  let gap : ℝ := (Real.log 2) ^ 2 - 4 * ell₀
  ((2956130689948496583556320428839528 : ℝ) /
      10000000000000000000000000000000000 < gap) ∧
    (gap <
      (2956130689948496583556320428839529 : ℝ) /
        10000000000000000000000000000000000) ∧
      0 < gap

end

end MathlibPlus.Open.Analysis.CompletedThetaCenterGapClaim15149
