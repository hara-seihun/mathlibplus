import MathlibPlus.Open.LorentzDeterminant

namespace MathlibPlus.Open.NewResearch2.Lorentz

noncomputable section

open MathlibPlus.Open

/-- Claim 7352: the two separate orientation inequalities place the
translated boundary matrix in the chosen signature-`(1,1)` time-oriented
Lorentz component. -/
def claim7352 : Prop :=
  ∀ (χ ζ ψ : ℝ),
    0 < χ →
    ψ < 4 →
    0 < lorentzL χ ζ ψ ∧ lorentzTimeOriented χ ζ ψ

end

end MathlibPlus.Open.NewResearch2.Lorentz
