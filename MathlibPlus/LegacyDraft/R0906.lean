import Mathlib

namespace MathlibPlus.LegacyDraft.R0906

/-- Claim 43285: the corrected fourth projective-row cumulant identity.
The scalar, ordinary-row, and interpolation equations are explicit hypotheses;
this is the branch-local algebraic conversion they imply. -/
theorem correctedFourthCumulant_algebra :
    ∀ (V A₁ A₂ D₂ D₃ E₃ J L W σ : ℚ),
      let Q := A₂ + V ^ 2 / 2
      let fold := σ * (6 * Q ^ 2 - 4 * Q * V ^ 2 + V ^ 4) / 4
      V * D₃ = A₂ ^ 2 + V ^ 4 / 12 →
      V ^ 2 * W = 2 * V * Q * J - L * Q ^ 2 + σ * Q ^ 3 →
      J = D₂ + V * A₁ →
      L = A₁ →
      W = E₃ + V * D₂ + A₁ * Q + fold →
      V ^ 2 * E₃ =
        V * (2 * Q - V ^ 2) * D₂ + A₁ * Q * (V ^ 2 - Q) +
          σ * (Q ^ 3 - V ^ 2 * (6 * Q ^ 2 - 4 * Q * V ^ 2 + V ^ 4) / 4) := by
  intro V A₁ A₂ D₂ D₃ E₃ J L W σ Q fold
  intro _hscalar hrow hJ hL hW
  rw [hW, hJ, hL] at hrow
  linear_combination hrow

end MathlibPlus.LegacyDraft.R0906
