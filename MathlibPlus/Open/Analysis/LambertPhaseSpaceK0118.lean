import MathlibPlus.Support.LambertJacobiCounting

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.Analysis.K0118

open MathlibPlus.Support.LambertJacobiCounting

/-- The constant-path phase fraction, with the active range convention from
`0 ≤ s ≤ 1`. -/
def lambertPhase (s : ℝ) : ℝ :=
  if 0 ≤ s ∧ s ≤ 1 then Real.pi⁻¹ * Real.arccos s else 0

/-- The multiplicative phase sum built from the canonical Lambert Jacobi
coefficient family.  The zero index is excluded, so the sum is over `j ≥ 1`. -/
def lambertBlockPhaseSum (κ T : ℝ) : ℝ :=
  ∑' j : ℕ,
    if 0 < j then
      lambertPhase (1 / (2 * T * jacobiCoeff κ j))
    else 0

/-- The spectral count of the canonical Lambert Jacobi operator differs from
its multiplicative block phase sum by `o(T)` at infinity. -/
def multiplicativeBlockPhaseSpaceCountingLemma : Prop :=
  ∀ (κ : ℝ) (hκ : 0 < κ),
    Asymptotics.IsLittleO (Filter.atTop : Filter ℝ)
      (fun T : ℝ =>
        (lambertJacobiCount κ hκ T : ℝ) - lambertBlockPhaseSum κ T)
      (fun T : ℝ => T)

end MathlibPlus.Open.Analysis.K0118

end
