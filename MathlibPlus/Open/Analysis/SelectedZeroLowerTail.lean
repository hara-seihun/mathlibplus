import Mathlib

open scoped BigOperators Interval Topology
open Filter MeasureTheory

namespace MathlibPlus.Open.Analysis.SelectedZeroLowerTail

/-- The integer value of `Γ(k)` used by the selected-zero formula for `k ≥ 1`. -/
noncomputable def gammaNat (k : ℕ) : ℝ :=
  (Nat.factorial (k - 1) : ℝ)

/-- The lower incomplete gamma integral with integer shape. -/
noncomputable def lowerGammaNat (k : ℕ) (z : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..z, y ^ (k - 1) * Real.exp (-y)

/-- The exact selected-zero contribution from Claim 15260, with
`A_{ρ,k}(X) = -Γ(k)⁻¹ ∫₀^{log X} y^(k-1) exp(-d y) dy` for `k ≥ 1`.
The value at `k = 0` is only a totalization and is irrelevant to the
atTop statement below. -/
noncomputable def selectedZeroContribution (k : ℕ) (d X : ℝ) : ℝ :=
  if 1 ≤ k then
    -(1 / gammaNat k) *
      ∫ y in (0 : ℝ)..Real.log X,
        y ^ (k - 1) * Real.exp (-d * y)
  else 0

/-- The lower-tail rate `I_-(u)=u-1-log u` on `0<u<1`, and zero on the
exponential scale for `u ≥ 1`. -/
noncomputable def lowerTailRate (u : ℝ) : ℝ :=
  if 0 < u ∧ u < 1 then u - 1 - Real.log u else 0

/-- Claim 15262.  At the cutoff `X = exp(rk/d)`, the selected-zero
contribution has the full exponential scale
`|A_{ρ,k}(X)| = d^(-k) exp(-k I_-(r) + o(k))`; the `-log d` term is
retained in the logarithmic formulation. -/
def lowerTailLargeDeviationRate : Prop :=
  ∀ d r : ℝ, 0 < d → 0 < r →
    Tendsto
      (fun k : ℕ =>
        if k = 0 then 0 else
          (1 / (k : ℝ)) * Real.log
            (|selectedZeroContribution k d
                (Real.exp (r * (k : ℝ) / d))|)) atTop
      (𝓝 (-(Real.log d) - lowerTailRate r))

end MathlibPlus.Open.Analysis.SelectedZeroLowerTail
