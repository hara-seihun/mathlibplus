import MathlibPlus.Open.ResearchFormalization.R0100LaguerreFlags

namespace MathlibPlus.Open.ResearchFormalization.R0100LaguerreTransformClaim17938

open MeasureTheory Set
open MathlibPlus.Open.ResearchFormalization.R0100LaguerreFlags

noncomputable section

/-- Claim 17938.  The positive-particle Laguerre carrier, the half-Mellin
convention, the common absolute-convergence half-plane, and the meromorphic
continuation are all retained in the shared reviewed R-0100 carriers. -/
def mellinLaguerrePochhammerTransform_claim17938 : Prop :=
  ∀ (n : ℕ) (α : ℝ),
    MeromorphicOn
        (fun s : ℂ =>
          pochhammer ((α : ℂ) + 1 - s / 2) n /
              (Nat.factorial n : ℂ) * completedZeta s)
        Set.univ ∧
      ∀ s : ℂ, 1 < s.re →
        halfMellinAbsolutelyConvergent
            (exponentialLaguerreTheta n α) s ∧
          halfMellin (exponentialLaguerreTheta n α) s =
            pochhammer ((α : ℂ) + 1 - s / 2) n /
              (Nat.factorial n : ℂ) * completedZeta s

end

end MathlibPlus.Open.ResearchFormalization.R0100LaguerreTransformClaim17938
