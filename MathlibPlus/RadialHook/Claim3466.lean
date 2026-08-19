import MathlibPlus.Open.Analysis.O0317Claims14137And14148

namespace MathlibPlus.RadialHook

noncomputable section

/-- Claim 3466: the Riesz energy density after `x = exp (2u)` is the
critical-log density with the Jacobian `2 exp (2u)`. -/
def rieszEnergyDensity_changeOfVariables_claim3466 : Prop :=
  ∀ u : ℝ,
    (|MathlibPlus.Open.Analysis.O0317.rieszFunction (Real.exp (2 * u))| ^ 2 /
        Real.rpow (Real.exp (2 * u)) (3 / 2 : ℝ)) *
        (2 * Real.exp (2 * u)) =
      2 *
        |Real.exp (-u / 2) *
            MathlibPlus.Open.Analysis.O0317.rieszFunction (Real.exp (2 * u))| ^ 2

end

end MathlibPlus.RadialHook
