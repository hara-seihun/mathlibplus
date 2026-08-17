import MathlibPlus.Open.Analysis.CenterFlatCompactSourceClaim15459
import MathlibPlus.Open.ResearchFormalization.O0328LogDerivativeAndFibers

namespace MathlibPlus.Open.ResearchFormalization.O0328SuperexponentialDecay15475

open Filter
open scoped Topology

noncomputable section

/-- The prescribed imaginary sample of the canonical centered multiplier. -/
noncomputable def oddIntegerMultiplierSample
    (q : ℝ → ℝ) (n : ℕ) : ℂ :=
  MathlibPlus.Open.ResearchFormalization.O0328LogDerivativeAndFibers.centeredMultiplier
    q (-Complex.I * (2 * (n : ℂ) + (1 / 2 : ℂ)))

/-- The real root-decay scale of the absolute value of a multiplier sample. -/
noncomputable def oddIntegerMultiplierSampleRoot
    (q : ℝ → ℝ) (n : ℕ) : ℝ :=
  Real.rpow ‖oddIntegerMultiplierSample q n‖ (1 / (2 * (n : ℝ)))

/-- Claim 15475: compact-source samples have superexponential root decay,
and the samples themselves converge to zero. -/
def claim15475 : Prop :=
  ∀ (a R : ℝ),
    0 < a →
    a < R →
      ∀ q : ℝ → ℝ,
        q ∈
            MathlibPlus.Open.Analysis.CenterFlatCompactSourceClaim15459.centerFlatSourceClass
              a R →
          Tendsto (oddIntegerMultiplierSampleRoot q) atTop (𝓝 0) ∧
            Tendsto (oddIntegerMultiplierSample q) atTop (𝓝 0)

end

end MathlibPlus.Open.ResearchFormalization.O0328SuperexponentialDecay15475
