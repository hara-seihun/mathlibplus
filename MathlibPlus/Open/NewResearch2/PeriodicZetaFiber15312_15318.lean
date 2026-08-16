import Mathlib
import MathlibPlus.Open.NewResearch2.LimitingResidual15317

open Filter MeasureTheory
open scoped BigOperators Topology ENNReal

namespace MathlibPlus.Open.NewResearch2.PeriodicZetaFiber

noncomputable section

/-- The logarithmic scale attached to an integral base. -/
def qLog (q : ℕ) : ℝ :=
  Real.log (q : ℝ)

/-- The radius `q^(-1/2)` in the commensurate coordinate. -/
def qRadius (q : ℕ) : ℝ :=
  Real.rpow (q : ℝ) (-(1 : ℝ) / 2)

/-- The critical-line period `T_q = 2π/log q`. -/
def qPeriod (q : ℕ) : ℝ :=
  2 * Real.pi / qLog q

/-- The singular-inner exponential in the Cayley coordinate. -/
def qPhi (q : ℕ) (z : ℂ) : ℂ :=
  MathlibPlus.Open.NewResearch2.LimitingResidual15317.geometricPhi q z

/-- The fully inner-divided normalized quotient, including the removable
zeta-residual value at the origin. -/
def qResidualDisk (q : ℕ) (z : ℂ) : ℂ :=
  MathlibPlus.Open.NewResearch2.LimitingResidual15317.zetaResidual z *
    (1 - (qRadius q : ℂ) * qPhi q z) /
      (1 - (qRadius q : ℂ) ^ 2)

/-- The Cayley point corresponding to `s = 1/2 + it`. -/
def qCriticalPoint (t : ℝ) : ℂ :=
  MathlibPlus.Open.NewResearch2.LimitingResidual15317.criticalDiskPoint t

/-- The boundary function `H_q` on the critical line. -/
def qCriticalBase (q : ℕ) (t : ℝ) : ℂ :=
  qResidualDisk q (qCriticalPoint t)

/-- Measurable periodic multipliers in the fixed-base relaxation. -/
def qPeriodicMultiplier (q : ℕ) (g : ℝ → ℂ) : Prop :=
  Measurable g ∧ Function.Periodic g (qPeriod q)

/-- The density in the critical-Cauchy squared loss. -/
def qCauchyDensity (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (2 * Real.pi * (1 / 4 + t ^ 2)))

/-- The measure with the exact critical-Cauchy density. -/
noncomputable def qCauchyMeasure : Measure ℝ :=
  Measure.withDensity volume qCauchyDensity

/-- The nonnegative extended-real loss of a measurable periodic multiplier. -/
noncomputable def qWeightedLoss (q : ℕ) (g : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ t : ℝ, ENNReal.ofReal (‖g t * qCriticalBase q t - 1‖ ^ 2)
    ∂qCauchyMeasure

/-- The relaxed periodic-fiber distance. -/
noncomputable def qDelta (q : ℕ) : ℝ≥0∞ :=
  sInf {δ : ℝ≥0∞ |
    ∃ g : ℝ → ℂ, qPeriodicMultiplier q g ∧ δ = qWeightedLoss q g}

/-- The exact greatest-lower-bound characterization of the relaxed distance;
the loss carrier itself is the specified measurable periodic class and
nonnegative extended integral. -/
def claim_15312 : Prop :=
  ∀ q : ℕ, 2 ≤ q →
    (∀ g : ℝ → ℂ,
      qPeriodicMultiplier q g →
        qDelta q ≤ qWeightedLoss q g) ∧
    (∀ δ : ℝ≥0∞,
      (∀ g : ℝ → ℂ,
        qPeriodicMultiplier q g →
          δ ≤ qWeightedLoss q g) →
        δ ≤ qDelta q)

/-- At every fixed integral base, arbitrary measurable periodic multipliers
remain at positive distance from the constant one. -/
def claim_15316 : Prop :=
  ∀ q : ℕ, 2 ≤ q → 0 < qDelta q

/-- The pole-removed zeta residual in the `s`-plane, totalized at its
removable value `s = 1`. -/
def calZetaResidual (s : ℂ) : ℂ :=
  if s = 1 then 1 else ((s - 1) / s) * riemannZeta s

/-- The nonvanishing periodic factor on the critical line. -/
def qCriticalFactor (q : ℕ) (t : ℝ) : ℂ :=
  (1 - (qRadius q : ℂ) *
      Complex.exp (-Complex.I * ((qLog q * t : ℝ) : ℂ))) /
    (1 - (qRadius q : ℂ) ^ 2)

/-- Vertical periodicity of the pole-removed residual on the analytic domain
`Re(s) > 1/2`. -/
def qHalfPlanePeriodicity (q : ℕ) : Prop :=
  ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
    calZetaResidual (s + Complex.I * (qPeriod q : ℂ)) =
      calZetaResidual s

/-- The exact critical-line factorization transferred from the Cayley
coordinate to the pole-removed zeta residual. -/
def qCriticalFactorization (q : ℕ) : Prop :=
  ∀ t : ℝ,
    qCriticalBase q t =
      qCriticalFactor q t *
        calZetaResidual ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)

/-- The large-real-part asymptotic obstruction and its eventual nonvanishing
conclusion. -/
def qLargeRealObstruction (q : ℕ) : Prop :=
  ∃ C σ₀ : ℝ, 0 ≤ C ∧ 0 < σ₀ ∧
    ∀ σ : ℝ, σ₀ ≤ σ →
      ‖calZetaResidual ((σ : ℂ) + Complex.I * (qPeriod q : ℂ)) -
          calZetaResidual (σ : ℂ) -
          (((1 / σ : ℝ) : ℂ) -
            1 / ((σ : ℂ) + Complex.I * (qPeriod q : ℂ)))‖ ≤
        C * Real.rpow 2 (-σ) ∧
      calZetaResidual ((σ : ℂ) + Complex.I * (qPeriod q : ℂ)) -
          calZetaResidual (σ : ℂ) ≠ 0

/-- The fixed-base residual cannot acquire the period supplied by the
commensurate geometric factor.  The transfer keeps the stated half-plane
and the explicit large-real contradiction. -/
def claim_15315 : Prop :=
  ∀ q : ℕ, 2 ≤ q →
    (∀ t : ℝ, qCriticalFactor q t ≠ 0) ∧
    Function.Periodic (qCriticalFactor q) (qPeriod q) ∧
    qCriticalFactorization q ∧
    (Function.Periodic (qCriticalBase q) (qPeriod q) →
      qHalfPlanePeriodicity q) ∧
    qLargeRealObstruction q ∧
    ¬ qHalfPlanePeriodicity q ∧
    ¬ Function.Periodic (qCriticalBase q) (qPeriod q)

/-- A global absolutely-continuous `W^{1,1}` representative.  The integral
identity records the derivative carrier directly, while both the function and
the derivative are required to be integrable. -/
def globalW11 (f f' : ℝ → ℂ) : Prop :=
  Continuous f ∧
    Integrable f volume ∧
      Integrable f' volume ∧
        ∀ a b : ℝ, a ≤ b →
          f b - f a = ∫ t in Set.Ioc a b, f' t

/-- Uniform shifted-lattice Riemann summation on the exact `W^{1,1}` carrier. -/
def claim_15318 : Prop :=
  ∀ (f f' : ℝ → ℂ), globalW11 f f' →
    ∀ T : ℝ, 0 < T →
      ∀ x : ℝ,
        Summable (fun k : ℤ => f (x + (k : ℝ) * T)) ∧
          ‖T • (∑' k : ℤ, f (x + (k : ℝ) * T)) - ∫ t : ℝ, f t‖ ≤
            T * ∫ t : ℝ, ‖f' t‖

end

end MathlibPlus.Open.NewResearch2.PeriodicZetaFiber
