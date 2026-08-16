import Mathlib

noncomputable section

open scoped BigOperators
open Filter Asymptotics MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization

/-- The completed zeta function used by the centered-square construction. -/
def xi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) *
      Complex.exp (-(s / 2) * Complex.log (Real.pi : ℂ)) *
      Complex.Gamma (s / 2) * riemannZeta s

/-- The centered xi function and its single-valued square-variable form. -/
def centeredX (z : ℂ) : ℂ := xi ((1 / 2 : ℂ) + z)

def centeredE (q : ℂ) : ℂ := centeredX (Complex.sqrt q)

def qPlus (t : ℝ) (z : ℂ) : ℂ :=
  (z + (t : ℂ) * Complex.I) ^ 2 / z

def qMinus (t : ℝ) (z : ℂ) : ℂ :=
  (z - (t : ℂ) * Complex.I) ^ 2 / z

def centeredF (t : ℝ) (z : ℂ) : ℂ :=
  (centeredE (qPlus t z) - centeredE (qMinus t z)) /
    ((t : ℂ) * Complex.I * (centeredE (qPlus t z) + centeredE (qMinus t z)))

def centeredD (t : ℝ) (z : ℂ) : ℂ :=
  centeredE (qPlus t z) + centeredE (qMinus t z)

/-- High-energy asymptotic and the derivative consequence. -/
def highEnergyAsymptotic : Prop :=
  ∀ t : ℝ, t ≠ 0 →
    Asymptotics.IsBigO atTop
      (fun x : ℝ =>
        centeredF t (x : ℂ) -
          Complex.ofReal
            ((Real.log x - 2 * Real.log (2 * Real.pi)) / (4 * Real.sqrt x) +
              7 / (4 * x)))
      (fun x : ℝ =>
        Complex.ofReal ((1 + (Real.log x) ^ 3) / Real.rpow x (3 / 2))) ∧
    Tendsto
      (fun x : ℝ => deriv (fun y : ℝ => centeredF t (y : ℂ)) x)
      atTop (nhds (0 : ℂ))

/-- The Riemann-hypothesis context used by the measure statement. -/
def RiemannHypothesis : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = (1 / 2 : ℝ)

/-- A direct Stieltjes measure for the transform, including its support and tail
integrability. -/
def DirectStieltjesRepresentation (t : ℝ) (μ : Measure ℝ) : Prop :=
  μ (Set.Ioi (1 / 4 : ℝ)) = 0 ∧
    Integrable (fun u : ℝ => (1 + |u|)⁻¹) μ ∧
    ∀ z : ℂ,
      ¬ (z.im = 0 ∧ z.re ≤ (1 / 4 : ℝ)) →
        centeredF t z = ∫ u : ℝ, (z - (u : ℂ))⁻¹ ∂μ

/-- The measure-theoretic meaning of pure point in this statement. -/
def IsPurePointMeasure (μ : Measure ℝ) : Prop :=
  ∀ s : Set ℝ, MeasurableSet s →
    μ s = ∑' u : ℝ, μ (s ∩ ({u} : Set ℝ))

/-- A pole is a norm blow-up at an isolated point. -/
def IsPoleAt (f : ℂ → ℂ) (z : ℂ) : Prop :=
  ∀ R : ℝ, ∃ δ : ℝ, 0 < δ ∧
    ∀ w : ℂ, 0 < ‖w - z‖ → ‖w - z‖ < δ → R < ‖f w‖

/-- A simple pole has a nonvanishing derivative of the reciprocal extension. -/
def IsSimplePoleAt (f : ℂ → ℂ) (z : ℂ) : Prop :=
  IsPoleAt f z ∧ f z = 0 ∧
    ∃ c : ℂ, c ≠ 0 ∧ HasDerivAt (fun w : ℂ => (f w)⁻¹) c z

/-- Exact positive atom/residue assertion at every simple real denominator zero. -/
def AtomResidueFormula (t : ℝ) (μ : Measure ℝ) : Prop :=
  ∀ u : ℝ, u ≠ 0 → centeredD t (u : ℂ) = 0 →
    deriv (fun z : ℂ => centeredD t z) (u : ℂ) ≠ 0 →
      μ ({u} : Set ℝ) ≠ ⊤ ∧
        0 < ENNReal.toReal (μ ({u} : Set ℝ)) ∧
        Complex.ofReal (ENNReal.toReal (μ ({u} : Set ℝ))) =
          (centeredE (qPlus t (u : ℂ)) - centeredE (qMinus t (u : ℂ))) /
            ((t : ℂ) * Complex.I *
              deriv (fun z : ℂ => centeredD t z) (u : ℂ))

/-- Pure-point measure, exact positive residues, and real simple poles in the
RH/domain context. -/
def purePointMeasureAndPoles : Prop :=
  RiemannHypothesis →
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ t : ℝ, 0 < t → t < t₀ →
        ∃ μ : Measure ℝ,
          DirectStieltjesRepresentation t μ ∧
          IsPurePointMeasure μ ∧
          AtomResidueFormula t μ ∧
          μ ({0} : Set ℝ) = 0 ∧
          (∀ z : ℂ, IsPoleAt (centeredF t) z →
            z.im = 0 ∧ IsSimplePoleAt (centeredF t) z) ∧
          (∀ ν : Measure ℝ, DirectStieltjesRepresentation t ν → ν = μ)

end MathlibPlus.Open.ResearchFormalization
