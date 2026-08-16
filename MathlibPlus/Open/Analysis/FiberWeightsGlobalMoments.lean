import MathlibPlus.Open.Analysis.LargeBaseFiberFloor

open scoped BigOperators ENNReal Topology
open Filter MeasureTheory

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- Absolute continuity on every finite real interval together with a global
`W^{1,1}` bound.  The codomain is allowed to be real or complex. -/
def researchW11Bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (K : ℝ) : Prop :=
  (∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b) ∧
    Integrable f volume ∧
    Integrable (deriv f) volume ∧
    (∫ t : ℝ, ‖f t‖) + (∫ t : ℝ, ‖deriv f t‖) ≤ K

/-- The limiting Hardy residual `H(z)`, including its removable value at zero. -/
def limitingH (z : ℂ) : ℂ :=
  if z = 0 then 1 else z * riemannZeta (1 / (1 - z))

/-- The boundary function of the limiting residual on the critical Cauchy line. -/
def limitingHBoundary (t : ℝ) : ℂ :=
  limitingH (criticalCoordinate t)

/-- The three exact real/complex functions to which the shifted-lattice estimate
is applied. -/
def weightedConjugate (q : ℕ) (t : ℝ) : ℂ :=
  (criticalCauchyDensity t : ℂ) * star (criticalBase q t)

def weightedEnergy (q : ℕ) (t : ℝ) : ℝ :=
  criticalCauchyDensity t * ‖criticalBase q t‖ ^ 2

/-- The global conjugate first moment of the limiting residual. -/
def limitingConjugateMoment : ℂ :=
  ∫ t : ℝ, star (limitingHBoundary t) ∂criticalCauchyMeasure

/-- The global second moment, i.e. the squared critical-Cauchy `H²` norm. -/
def limitingH2Energy : ℝ :=
  ∫ t : ℝ, ‖limitingHBoundary t‖ ^ 2 ∂criticalCauchyMeasure

/-- Uniform convergence on the varying fundamental fiber `[0,T_q)`. -/
def fiberUniformReal (f : ℕ → ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ q in atTop, ∀ x : ℝ, 0 ≤ x → x < fiberPeriod q →
      |f q x - a| < ε

def fiberUniformComplex (f : ℕ → ℝ → ℂ) (a : ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ q in atTop, ∀ x : ℝ, 0 ≤ x → x < fiberPeriod q →
      ‖f q x - a‖ < ε

/-- Claim 15319: uniform `W^{1,1}` control of the exact density, conjugate
fiber weight, and energy fiber weight forces the three shifted-lattice sums to
converge uniformly on each varying fiber to their global limiting moments. -/
def fiberWeightsConvergeToGlobalMoments : Prop :=
  (∃ K : ℝ, 0 ≤ K ∧
      researchW11Bound criticalCauchyDensity K ∧
      ∀ q : ℕ,
        researchW11Bound (weightedConjugate q) K ∧
          researchW11Bound (weightedEnergy q) K) →
    limitingConjugateMoment = (1 : ℂ) ∧
      fiberUniformReal
        (fun q x => fiberPeriod q * fiberD q x) 1 ∧
      fiberUniformComplex
        (fun q x => (fiberPeriod q : ℂ) * fiberC q x)
        limitingConjugateMoment ∧
      fiberUniformReal
        (fun q x => fiberPeriod q * fiberA q x) limitingH2Energy

end

end MathlibPlus.Open.Analysis
