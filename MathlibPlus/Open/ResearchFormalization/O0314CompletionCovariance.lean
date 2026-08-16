import Mathlib
import MathlibPlus.Open.ResearchFormalization.O0314CompletedPair

namespace MathlibPlus.Open.ResearchFormalization.O0314

noncomputable section

/-- The zeta functional-equation covariance factor from the O-0314 source. -/
noncomputable def standardCompletionCovarianceFactor (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (s - (1 / 2 : ℂ)) *
    Complex.Gamma ((1 - s) / 2) / Complex.Gamma (s / 2)

/-- Points at which both gamma factors in the covariance identity are regular.
The nonvanishing formulation avoids assigning meromorphic poles the value
provided by Mathlib's totalized Gamma. -/
def completionCovarianceRegular (s : ℂ) : Prop :=
  Complex.Gamma (s / 2) ≠ 0 ∧
    Complex.Gamma ((1 - s) / 2) ≠ 0

/-- Claim 15337: the displayed completion covariance, as a meromorphic
identity, agrees pointwise on the common regular locus. -/
def claim15337 : Prop :=
  Meromorphic standardCompletionFactor ∧
    Meromorphic standardCompletionCovarianceFactor ∧
    Meromorphic (fun s : ℂ => standardCompletionFactor (1 - s)) ∧
    Meromorphic (fun s : ℂ =>
      standardCompletionCovarianceFactor s * standardCompletionFactor s) ∧
    (∀ s : ℂ, completionCovarianceRegular s →
      standardCompletionFactor (1 - s) =
        standardCompletionCovarianceFactor s * standardCompletionFactor s)

end

end MathlibPlus.Open.ResearchFormalization.O0314
