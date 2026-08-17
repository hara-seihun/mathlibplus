import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.Analysis.Claim18793

noncomputable def scaledCombMeasure (r : ℝ) : Measure ℝ :=
  Measure.sum (fun n : ℤ => Measure.dirac (r * (n : ℝ)))

noncomputable def thetaCombMeasure : Measure ℝ :=
  scaledCombMeasure 1

noncomputable def perturbedCombMeasure (a ε : ℝ) : Measure ℝ :=
  thetaCombMeasure +
    ENNReal.ofReal ε •
      (scaledCombMeasure (Real.sqrt a) +
        ENNReal.ofReal (Real.rpow a (-1 / 2 : ℝ)) •
          scaledCombMeasure (1 / Real.sqrt a))

noncomputable def schwartzPairing
    (μ : Measure ℝ) (φ : SchwartzMap ℝ ℂ) : ℂ :=
  ∫ x : ℝ, φ x ∂μ

noncomputable def fourierTest
    (φ : SchwartzMap ℝ ℂ) (x : ℝ) : ℂ :=
  ∫ y : ℝ,
    Complex.exp
      (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * (y : ℂ)) * φ y

/-- These are the source properties of the explicit positive pure-point path:
the measure is tested for positivity, Schwartz integrability, and Fourier
self-duality rather than replaced by an unconstrained abstract callback. -/
def positiveTemperedFourierSelfDual
    (μ : Measure ℝ) : Prop :=
  (∀ φ : SchwartzMap ℝ ℝ,
    (∀ x : ℝ, 0 ≤ φ x) →
      0 ≤ ∫ x : ℝ, φ x ∂μ) ∧
    (∀ φ : SchwartzMap ℝ ℂ,
      Integrable (fun x : ℝ => φ x) μ) ∧
    (∀ φ : SchwartzMap ℝ ℂ,
      schwartzPairing μ φ =
        ∫ x : ℝ, fourierTest φ x ∂μ)

def offAxisMultiplierZero (a ε : ℝ) : Prop :=
  ∃ z : ℂ,
    z.re ≠ 0 ∧
      1 + 2 * (ε : ℂ) *
          (Real.rpow a (-1 / 4 : ℝ) : ℂ) *
          Complex.cosh (((Real.log a / 2 : ℝ) : ℂ) * z) = 0

noncomputable def finiteSchwartzPairingData
    (μ : Measure ℝ) {n : ℕ}
    (φ : Fin n → SchwartzMap ℝ ℂ) : Fin n → ℂ :=
  fun i => schwartzPairing μ (φ i)

/-- Claim 18793: no criterion that is continuous in finitely many actual
Schwartz pairings separates the theta comb from the explicit positive,
Fourier-self-dual, off-axis perturbation path. -/
def finiteSchwartzPairingsCannotSeparateTheta_claim18793 : Prop :=
  ∀ a : ℝ, 1 < a →
    (∀ ε : ℝ, 0 < ε →
      positiveTemperedFourierSelfDual (perturbedCombMeasure a ε)) ∧
    (∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → offAxisMultiplierZero a ε) ∧
    (∀ (n : ℕ) (φ : Fin n → SchwartzMap ℝ ℂ),
      Filter.Tendsto
        (fun ε : ℝ => finiteSchwartzPairingData
          (perturbedCombMeasure a ε) φ)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds (finiteSchwartzPairingData thetaCombMeasure φ))) ∧
    ∀ (n : ℕ) (φ : Fin n → SchwartzMap ℝ ℂ)
      (criterion : (Fin n → ℂ) → Bool),
      Continuous criterion →
        ¬ (criterion (finiteSchwartzPairingData thetaCombMeasure φ) = true ∧
          ∃ ε₀ : ℝ, 0 < ε₀ ∧
            ∀ ε : ℝ, 0 < ε → ε < ε₀ →
              criterion (finiteSchwartzPairingData
                (perturbedCombMeasure a ε) φ) = false)

end MathlibPlus.Open.Analysis.Claim18793
