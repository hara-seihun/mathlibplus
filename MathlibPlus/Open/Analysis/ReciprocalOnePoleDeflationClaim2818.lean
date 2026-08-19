import MathlibPlus.Open.Basic
import MathlibPlus.Analysis.ReciprocalXi

namespace MathlibPlus.Open.Analysis

/-- Claim 2818: the reciprocal function and its one-pole deflation. -/
noncomputable def reciprocalOnePoleDeflation_claim2818 (γm : ℝ) : Prop :=
  let A : ℂ → ℂ := fun z =>
    MathlibPlus.Analysis.ReciprocalXi.xi
      ((1 / 2 : ℂ) + Complex.sqrt z)
  let A_m : ℂ → ℂ := fun z =>
    A z / (1 + z / (γm : ℂ) ^ 2)
  let H : ℂ → ℂ := fun t => A 0 / A (-t)
  let H_m : ℂ → ℂ := fun t => A 0 / A_m (-t)
  ∀ t : ℂ,
    H_m t = (1 - t / (γm : ℂ) ^ 2) * H t

end MathlibPlus.Open.Analysis
