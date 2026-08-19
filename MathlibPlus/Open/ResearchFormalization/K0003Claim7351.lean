import MathlibPlus.Open.LorentzDeterminant
import MathlibPlus.Open.Analysis.LorentzIncrement

namespace MathlibPlus.Open.ResearchFormalization.K0003Claim7351

open MathlibPlus.Open
open MathlibPlus.Open.Analysis

noncomputable section

/-- The translated Lorentz boundary matrix and its determinant coordinate on
an indexed scalar state, with the completed boundary retained as ψ-4. -/
def lorentzTranslateAndDeterminant_claim7351 : Prop :=
  ∀ (χ ζ ψ : ℕ → ℝ) (n : ℕ),
    lorentzH (χ n) (ζ n) (ψ n) =
        !![χ n, ζ n; ζ n, ψ n - 4] ∧
      lorentzL (χ n) (ζ n) (ψ n) =
        χ n * (4 - ψ n) + (ζ n) ^ 2 ∧
      lorentzL (χ n) (ζ n) (ψ n) =
        lorentzState (χ n) (ζ n) (ψ n)

end

end MathlibPlus.Open.ResearchFormalization.K0003Claim7351
