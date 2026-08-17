import Mathlib

namespace MathlibPlus.Open.Analysis.ResearchFormalizationR0186

noncomputable section

/-- Claim 18636: the second Wronskian of the explicit limiting tangent
curve from the parabolic-wall blowup has the displayed closed form. -/
def secondWronskianFormula_claim18636 : Prop :=
  let v : ℝ → Fin 3 → ℝ := fun Q =>
    ![ Real.tanh Q + Q * (Real.cosh Q)⁻¹ ^ 2,
       2 * Q,
       Q ^ 2 * (3 * Real.tanh Q + Q * (Real.cosh Q)⁻¹ ^ 2) ]
  ∀ Q : ℝ,
    Matrix.det
        (fun i j : Fin 2 =>
          iteratedDeriv (j : ℕ)
            (fun z : ℝ => v z (Fin.castLE (Nat.le_succ 2) i)) Q) =
      2 *
        (Real.tanh Q - Q * (Real.cosh Q)⁻¹ ^ 2 +
          2 * Q ^ 2 * (Real.cosh Q)⁻¹ ^ 2 * Real.tanh Q)

end
end MathlibPlus.Open.Analysis.ResearchFormalizationR0186
