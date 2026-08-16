import Mathlib

open scoped BigOperators Topology

namespace MathlibPlus.Open.NewResearch2.LimitingResidual15317

noncomputable section

/-- The critical-line boundary point of the disk coordinate. -/
def criticalDiskPoint (t : ℝ) : ℂ :=
  1 - 1 / ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)

/-- The removable zeta residual, with its central value represented as the
analytic continuation at the pole preimage. -/
def zetaResidual (z : ℂ) : ℂ :=
  if z = 0 then 1 else z * riemannZeta (1 / (1 - z))

/-- The geometric singular-inner coordinate in the q-family. -/
def geometricPhi (q : ℕ) (z : ℂ) : ℂ :=
  let L : ℝ := Real.log (q : ℝ)
  Complex.exp (-((L : ℂ) / 2) * ((1 + z) / (1 - z)))

/-- The q-dependent radius and period, written on the cofinal q+2 sequence. -/
def geometricRadius (q : ℕ) : ℝ :=
  Real.rpow ((q + 2 : ℕ) : ℝ) (- (1 : ℝ) / 2)

def geometricPeriod (q : ℕ) : ℝ :=
  2 * Real.pi / Real.log ((q + 2 : ℕ) : ℝ)

/-- The normalized geometric residual `H_q`. -/
def geometricResidual (q : ℕ) (z : ℂ) : ℂ :=
  zetaResidual z *
    (1 - (geometricRadius q : ℂ) * geometricPhi (q + 2) z) /
      (1 - (geometricRadius q) ^ 2)

/-- The critical-Cauchy weight and squared boundary norm. -/
def criticalCauchyWeight (t : ℝ) : ℝ :=
  1 / (2 * Real.pi * (1 / 4 + t ^ 2))

def criticalCauchyNormSquared (f : ℝ → ℂ) : ℝ :=
  ∫ t : ℝ, ‖f t‖ ^ 2 * criticalCauchyWeight t

/-- The limiting residual belongs to the critical-Cauchy Hardy carrier, and
its geometric residuals converge to it with vanishing radius and period. -/
def claim_15317 : Prop :=
  let H : ℂ → ℂ := zetaResidual
  let Hline : ℝ → ℂ := fun t => H (criticalDiskPoint t)
  let Hq : ℕ → ℝ → ℂ := fun q t =>
    geometricResidual q (criticalDiskPoint t)
  let A : ℝ := criticalCauchyNormSquared Hline
  AnalyticOnNhd ℂ H (Metric.ball 0 1) ∧
    H 0 = 1 ∧
    MeasureTheory.Integrable (fun t : ℝ => ‖Hline t‖ ^ 2 * criticalCauchyWeight t)
      MeasureTheory.volume ∧
    (∃ z₁ z₂ : ℂ,
      z₁ ∈ Metric.ball 0 1 ∧ z₂ ∈ Metric.ball 0 1 ∧ H z₁ ≠ H z₂) ∧
    A = 1 + ∫ t : ℝ,
      ‖Hline t - 1‖ ^ 2 * criticalCauchyWeight t ∧
    0 < ∫ t : ℝ,
      ‖Hline t - 1‖ ^ 2 * criticalCauchyWeight t ∧
    1 < A ∧
    Filter.Tendsto (fun q : ℕ => geometricRadius q) Filter.atTop (𝓝 0) ∧
    Filter.Tendsto (fun q : ℕ => geometricPeriod q) Filter.atTop (𝓝 0) ∧
    Filter.Tendsto
      (fun q : ℕ => ∫ t : ℝ,
        ‖Hq q t - Hline t‖ ^ 2 * criticalCauchyWeight t)
      Filter.atTop (𝓝 0)

end
end MathlibPlus.Open.NewResearch2.LimitingResidual15317
