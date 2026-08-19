import Mathlib
import MathlibPlus.Open.ResearchFormalization.BatchO0078

namespace MathlibPlus.Open.ResearchFormalization.BatchO0078.ShiftedPolarMomentsPhaseSpeedClaim12125

open MathlibPlus.Open.ResearchFormalization.BatchO0078

noncomputable section

/-- Claim 12125: the canonical normalized-Xi carrier has the three exact
shifted polar-moment formulas, with the phase speed and its derivative taken
from the reviewed gamma carrier. -/
def shiftedPolarMomentsAndPhaseSpeed_claim12125 : Prop :=
  ∀ (σ t : ℝ),
    normalizedXi 6 σ t = gammaPhase σ t * moment σ t 0 ∧
      deriv (fun u : ℝ => normalizedXi 6 σ u) t =
        Complex.I * gammaPhase σ t * moment σ t 1 ∧
      deriv (deriv (fun u : ℝ => normalizedXi 6 σ u)) t =
        gammaPhase σ t *
          (-moment σ t 2 +
            Complex.I * ((deriv (fun u : ℝ => q6 σ u) t : ℝ) : ℂ) * moment σ t 0)

end

end MathlibPlus.Open.ResearchFormalization.BatchO0078.ShiftedPolarMomentsPhaseSpeedClaim12125
