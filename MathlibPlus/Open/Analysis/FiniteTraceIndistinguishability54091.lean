import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.Analysis.FiniteTraceIndistinguishability54091

noncomputable section

/-- A measure is discrete when it is carried by a countable subset of the real line. -/
def IsDiscreteMeasure (μ : Measure ℝ) : Prop :=
  ∃ s : Set ℝ, s.Countable ∧ μ sᶜ = 0

/-- The super-exponential tail condition used by the heat-transform source class. -/
def HasSuperExponentialTails (μ : Measure ℝ) : Prop :=
  ∀ A : ℝ, 0 < A →
    Integrable (fun u : ℝ => Real.exp (A * u ^ 2)) μ

/-- Positive even discrete sources with super-exponential tails. -/
def PositiveEvenDiscreteSuperexponential (μ : Measure ℝ) : Prop :=
  IsDiscreteMeasure μ ∧
    Measure.map (fun u : ℝ => -u) μ = μ ∧
    HasSuperExponentialTails μ

/-- The heat transform of a real source measure. -/
noncomputable def heatTransform (μ : Measure ℝ) (t : ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ,
    Complex.exp
      (((t * u ^ 2 : ℝ) : ℂ) + Complex.I * z * (u : ℂ)) ∂μ

/-- The origin-time jet row fixed by the admitted analytic interface. -/
noncomputable def originJet (μ : Measure ℝ) (τ : ℝ) (k : ℕ) : ℂ :=
  ∫ u : ℝ,
    (((u ^ (2 * k) * Real.exp (τ * u ^ 2) : ℝ) : ℂ)) ∂μ

def targetTime : ℝ := 1479 / 10000

def targetHeight : ℝ := 1 / 10

def targetIndex : ℕ := 6000000185827

noncomputable def targetPoint : ℂ :=
  (((2 * (targetIndex : ℝ) + 1) * Real.pi : ℝ) : ℂ) +
    Complex.I * (targetHeight : ℂ)

/--
R-4946.7 (claim 54091): every finite list of origin-time observations admits
 distinct positive even discrete sources with the same listed jets, while
 their heat transforms differ at the fixed target point.
-/
def claim_54091 : Prop :=
  ∀ observations : List (ℝ × ℕ),
    ∃ μ₀ μ₁ : Measure ℝ,
      μ₀ ≠ μ₁ ∧
      PositiveEvenDiscreteSuperexponential μ₀ ∧
      PositiveEvenDiscreteSuperexponential μ₁ ∧
      (∀ j : Fin observations.length,
        originJet μ₀ (observations.get j).1 (observations.get j).2 =
          originJet μ₁ (observations.get j).1 (observations.get j).2) ∧
      heatTransform μ₀ targetTime targetPoint = 0 ∧
      heatTransform μ₁ targetTime targetPoint ≠ 0

end

end MathlibPlus.Open.Analysis.FiniteTraceIndistinguishability54091
