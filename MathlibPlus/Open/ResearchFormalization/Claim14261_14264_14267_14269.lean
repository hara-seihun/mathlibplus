import Mathlib

open scoped BigOperators
open MeasureTheory
open Set
open Classical

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a00bc5

/-- The factorial coefficients in the negative-even atomic measure. -/
def factorialCoefficient (m : ℕ) : ℝ :=
  (-1 : ℝ)^m * (2 * Real.pi)^(2 * m) / (2 * (2 * m).factorial)

/-- The negative even support occurring in the factorial measure. -/
def factorialNegativeEvenLattice : Set ℝ :=
  {x | ∃ m : ℕ, x = -((2 * (m + 1) : ℕ) : ℝ)}

/-- Exact custody data for the factorial negative-even signed measure. -/
def factorialMeasureData (μ : SignedMeasure ℝ) : Prop :=
  μ ≠ 0 ∧
    IsFiniteMeasure (SignedMeasure.totalVariation μ) ∧
    μ factorialNegativeEvenLatticeᶜ = 0 ∧
    (∀ s : Set ℝ, MeasurableSet s →
      μ s = ∑' m : ℕ,
        if -((2 * (m + 1) : ℕ) : ℝ) ∈ s then factorialCoefficient (m + 1) else 0) ∧
    (∀ m : ℕ,
      μ {-((2 * (m + 1) : ℕ) : ℝ)} = factorialCoefficient (m + 1)) ∧
    ENNReal.toReal (SignedMeasure.totalVariation μ Set.univ) =
      (Real.cosh (2 * Real.pi) - 1) / 2

/-- Claim 14264: the exact factorial negative-even shift measure and its variation. -/
def claim14264 : Prop :=
  ∃ μ : SignedMeasure ℝ, factorialMeasureData μ

/-- The signed integral used for bilateral transforms of real signed measures. -/
noncomputable def signedIntegralReal (μ : SignedMeasure ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ x, f x ∂μ.toJordanDecomposition.posPart) -
    (∫ x, f x ∂μ.toJordanDecomposition.negPart)

/-- The complex signed integral used for the entire transform. -/
noncomputable def signedIntegralComplex (μ : SignedMeasure ℝ) (f : ℝ → ℂ) : ℂ :=
  (∫ x, f x ∂μ.toJordanDecomposition.posPart) -
    (∫ x, f x ∂μ.toJordanDecomposition.negPart)

/-- The bilateral Laplace transform of the factorial signed measure. -/
noncomputable def factorialLaplace (μ : SignedMeasure ℝ) (t : ℝ) : ℝ :=
  signedIntegralReal μ (fun x => Real.exp (-x * t))

/-- Claim 14267: every integer logarithm, and hence every von Mangoldt atom, is annihilated. -/
def claim14267 : Prop :=
  ∃ μ : SignedMeasure ℝ,
    factorialMeasureData μ ∧
      (∀ n : ℕ, 1 ≤ n →
        factorialLaplace μ (Real.log (n : ℝ)) = 0) ∧
      (∀ n : ℕ, 2 ≤ n →
        ArithmeticFunction.vonMangoldt n * Real.log (n : ℝ) *
            factorialLaplace μ (Real.log (n : ℝ)) = 0)

/-- The exact high-frequency density for the factorial measure. -/
def factorialHighDensity (t : ℝ) : ℝ :=
  t * (Real.exp t - (Real.exp (2 * t) - 1)⁻¹) *
    (Real.sin (Real.pi * Real.exp t))^2

/-- The continuous high-frequency carrier on the half-line. -/
noncomputable def factorialHighCarrier : Measure ℝ :=
  Measure.withDensity (volume.restrict (Set.Ici (Real.log 2)))
    (fun t => ENNReal.ofReal (factorialHighDensity t))

/-- The high-frequency Laplace transform, written against its density. -/
noncomputable def factorialKHi (s : ℂ) : ℂ :=
  ∫ t in Set.Ici (Real.log 2),
    Complex.exp (-s * (t : ℂ)) * (factorialHighDensity t : ℂ)

/-- Its real-axis restriction. -/
noncomputable def factorialKHiReal (s : ℝ) : ℝ :=
  ∫ t in Set.Ici (Real.log 2),
    Real.exp (-s * t) * factorialHighDensity t

/-- Claim 14269: density bounds, holomorphy/nonzeroness, and complete monotonicity. -/
def claim14269 : Prop :=
  (∀ t : ℝ, Real.log 2 ≤ t →
    0 ≤ factorialHighDensity t ∧
      factorialHighDensity t ≤ t * Real.exp t) ∧
  AnalyticOnNhd ℂ factorialKHi {s : ℂ | 1 < s.re} ∧
  (∃ s : ℂ, 1 < s.re ∧ factorialKHi s ≠ 0) ∧
  (∀ (j : ℕ) (s : ℝ), 1 < s →
    (-1 : ℝ)^j * iteratedDeriv j factorialKHiReal s =
        ∫ t : ℝ, t^j * Real.exp (-s * t) ∂factorialHighCarrier ∧
      0 ≤ ∫ t : ℝ, t^j * Real.exp (-s * t) ∂factorialHighCarrier)

/-- The negative lattice of the Bernoulli convolution counterexample. -/
def negativeShiftLattice : Set ℝ :=
  {x | ∃ m : ℕ, x = -(m : ℝ) / Real.log 2}

/-- A finite signed negative-lattice measure with every exponential moment. -/
def negativeShiftMeasureData (μ : SignedMeasure ℝ) : Prop :=
  μ ≠ 0 ∧
    IsFiniteMeasure (SignedMeasure.totalVariation μ) ∧
    μ negativeShiftLatticeᶜ = 0 ∧
    (∀ r : ℝ,
      Integrable (fun x : ℝ => Real.exp (r * x))
        (SignedMeasure.totalVariation μ))

/-- The real bilateral transform of a negative-shift measure. -/
noncomputable def negativeShiftLaplace (μ : SignedMeasure ℝ) (t : ℝ) : ℝ :=
  signedIntegralReal μ (fun x => Real.exp (-x * t))

/-- The complex transform whose entire extension is asserted in Claim 14261. -/
noncomputable def negativeShiftEntireTransform (μ : SignedMeasure ℝ) (z : ℂ) : ℂ :=
  signedIntegralComplex μ (fun x => Complex.exp (-((x : ℂ) * z)))

/-- The completed-carrier multiplier. -/
def negativeShiftKappa (t : ℝ) : ℝ :=
  t * ((Real.exp (2 * t) - 1)⁻¹ - Real.exp t)

/-- The exact continuous density in the completed high-frequency carrier. -/
def negativeShiftCarrierDensity (M : ℝ → ℝ) (t : ℝ) : ℝ :=
  negativeShiftKappa t * M t

/-- The literal von Mangoldt atom coefficient in that carrier. -/
def negativeShiftAtomCoefficient (M : ℝ → ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * Real.log (n : ℝ) * M (Real.log (n : ℝ))

/-- The continuous part of the completed high-frequency carrier. -/
noncomputable def negativeShiftContinuousCarrier (M : ℝ → ℝ) : Measure ℝ :=
  Measure.withDensity (volume.restrict (Set.Ici (Real.log 2)))
    (fun t => ENNReal.ofReal (negativeShiftCarrierDensity M t))

/-- The literal atomic part of the completed high-frequency carrier. -/
noncomputable def negativeShiftAtomicCarrier (M : ℝ → ℝ) : Measure ℝ :=
  Measure.sum (fun n : ℕ =>
    if 2 ≤ n then
      ENNReal.ofReal (negativeShiftAtomCoefficient M n) •
        Measure.dirac (Real.log (n : ℝ))
    else 0)

/-- The completed high-frequency carrier appearing in the sign counterexample. -/
noncomputable def negativeShiftCarrier (M : ℝ → ℝ) : Measure ℝ :=
  negativeShiftContinuousCarrier M + negativeShiftAtomicCarrier M

/-- Exact positivity, support, and genuineness of the completed carrier. -/
def positiveHighFrequencyCarrier (M : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, Real.log 2 ≤ t → 0 ≤ negativeShiftCarrierDensity M t) ∧
    ContinuousOn (fun t => negativeShiftCarrierDensity M t)
      (Set.Ici (Real.log 2)) ∧
    (∀ n : ℕ, 2 ≤ n → negativeShiftAtomCoefficient M n = 0) ∧
    negativeShiftCarrier M ≠ 0 ∧
    IsLocallyFiniteMeasure (negativeShiftCarrier M) ∧
    negativeShiftCarrier M (Set.Iio (Real.log 2)) = 0

/-- The sign/prime-power uniqueness assertion refuted by the counterexample. -/
def primePowerSignUniqueness : Prop :=
  ∀ M : ℝ → ℝ,
    (∀ t : ℝ, Real.log 2 ≤ t → M t ≤ 0) →
    (∀ p k : ℕ, Nat.Prime p → 1 ≤ k →
      M (Real.log (((p ^ k : ℕ) : ℝ))) = 0) →
    M = 0

/-- Claim 14261: sign and all prime-power anchors do not force an entire transform to vanish. -/
def claim14261 : Prop :=
  ¬ primePowerSignUniqueness ∧
    ∃ μ : SignedMeasure ℝ,
      negativeShiftMeasureData μ ∧
      AnalyticOnNhd ℂ (negativeShiftEntireTransform μ) Set.univ ∧
      (∀ t : ℝ,
        negativeShiftEntireTransform μ (t : ℂ) =
          (negativeShiftLaplace μ t : ℂ)) ∧
      (∀ t : ℝ, Real.log 2 ≤ t → negativeShiftLaplace μ t ≤ 0) ∧
      (∀ p k : ℕ, Nat.Prime p → 1 ≤ k →
        negativeShiftLaplace μ (Real.log (((p ^ k : ℕ) : ℝ))) = 0) ∧
      (∃ t : ℝ, negativeShiftLaplace μ t ≠ 0) ∧
      positiveHighFrequencyCarrier (negativeShiftLaplace μ)

end MathlibPlus.Open.ResearchFormalizationBatch_01a00bc5
