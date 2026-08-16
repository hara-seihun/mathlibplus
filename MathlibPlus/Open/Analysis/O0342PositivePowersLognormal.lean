import Mathlib

open Filter MeasureTheory Set
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.O0342

noncomputable section

abbrev PositiveReal := {x : ℝ // 0 < x}

/-- The affine-normalized representative of a logarithm. -/
def affineNormalize (Y : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ :=
  fun s => Y s - (a + b * s)

/-- Complete monotonicity on the open terminal interval `(s₀, ∞)`, including
smoothness and all alternating derivative inequalities. -/
def completelyMonotoneOnTail (f : ℝ → ℝ) (s₀ : ℝ) : Prop :=
  ContDiffOn ℝ ⊤ f (Ioi s₀) ∧
    ∀ n : ℕ, ∀ s : ℝ, s₀ < s →
      0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n f s

/-- Infinite divisibility in the multiplicative cone of completely monotone
functions on a terminal interval. -/
def infinitelyDivisibleInCompletelyMonotoneCone
    (X : ℝ → ℝ) (s₀ : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n →
    ∃ f : ℝ → ℝ,
      completelyMonotoneOnTail f s₀ ∧
        ∀ s : ℝ, s₀ < s → X s = (f s) ^ n

/-- Every positive real power of `X` is completely monotone on the tail. -/
def allPositivePowersCompletelyMonotone (X : ℝ → ℝ) (s₀ : ℝ) : Prop :=
  ∀ θ : ℝ, 0 < θ →
    completelyMonotoneOnTail (fun s : ℝ => Real.rpow (X s) θ) s₀

/-- The measure obtained by multiplying a positive measure by its positive
coordinate, i.e. the inverse-Laplace carrier corresponding to `t ρ`. -/
noncomputable def inverseLaplaceCarrier (ρ : Measure ℝ) : Measure ℝ :=
  ρ.withDensity (fun t : ℝ => ENNReal.ofReal t)

/-- Claim 15570: positive powers force logarithmic complete monotonicity and a
nonnegative inverse-Laplace carrier, allowing the stated affine normalization. -/
def positivePowersLogCompleteMonotonicity_claim15570 : Prop :=
  ∀ (X Y : ℝ → ℝ) (s₀ : ℝ),
    (∃ a b : ℝ,
      let Y₀ := affineNormalize Y a b
      (∀ s : ℝ, s₀ < s → X s = Real.exp (Y₀ s)) ∧
        (∀ s : ℝ, s₀ < s → 0 < X s) ∧
        allPositivePowersCompletelyMonotone X s₀) →
    ∃ a b : ℝ,
      let Y₀ := affineNormalize Y a b
      (∀ s : ℝ, s₀ < s → X s = Real.exp (Y₀ s)) ∧
        (∀ s : ℝ, s₀ < s → 0 < X s) ∧
        allPositivePowersCompletelyMonotone X s₀ ∧
        infinitelyDivisibleInCompletelyMonotoneCone X s₀ ∧
        completelyMonotoneOnTail (fun s : ℝ => -deriv Y₀ s) s₀ ∧
        ∃ ρ : Measure ℝ,
          ρ (Ioi (0 : ℝ))ᶜ = 0 ∧
            IsLocallyFiniteMeasure ρ ∧
            Measure.Regular ρ ∧
            (∀ s : ℝ, s₀ < s →
              Integrable
                  (fun t : ℝ => t * Real.exp (-s * t)) ρ ∧
                deriv (deriv Y₀) s =
                  ∫ t in Ioi (0 : ℝ), t * Real.exp (-s * t) ∂ρ) ∧
            0 ≤ inverseLaplaceCarrier ρ

/-- The displayed lognormal signed density on the positive-real subtype. -/
noncomputable def lognormalDensity (σ : ℝ) (x : PositiveReal) : ℝ :=
  Real.exp (-((Real.log (x : ℝ)) ^ 2) / (2 * σ ^ 2)) / (x : ℝ) *
    (Real.exp (2 * Real.pi ^ 2 / σ ^ 2) *
        Real.cos (2 * Real.pi * Real.log (x : ℝ) / σ ^ 2) - 1)

/-- Lebesgue measure on the positive-real subtype. -/
noncomputable def positiveVolume : Measure PositiveReal :=
  Measure.comap Subtype.val (volume : Measure ℝ)

/-- The signed measure defined by the displayed density with respect to
Lebesgue measure on `(0, ∞)`. -/
noncomputable def lognormalSignedMeasure (σ : ℝ) : SignedMeasure PositiveReal :=
  positiveVolume.withDensityᵥ (lognormalDensity σ)

noncomputable def lognormalConstant (σ : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi) * σ

/-- The terms of the Carleman series for the total variation of the displayed
signed measure. The zero index is omitted. -/
noncomputable def lognormalCarlemanTerm (σ : ℝ) (j : ℕ) : ℝ :=
  if 0 < j then
    (∫ x : PositiveReal, (x : ℝ) ^ (2 * j) ∂(lognormalSignedMeasure σ).totalVariation) ^
      (-(1 : ℝ) / (2 * j))
  else 0

/-- Claim 15572: the explicit finite nonzero signed lognormal measure has the
Gaussian Mellin transform, integer zeros, and a convergent (non-Carleman)
series of even total-variation moments. -/
def explicitLognormalMomentIndeterminacy_claim15572 : Prop :=
  ∀ σ : ℝ, 0 < σ →
    Integrable (lognormalDensity σ) positiveVolume ∧
      let η := lognormalSignedMeasure σ
      η ≠ 0 ∧
        IsFiniteMeasure η.totalVariation ∧
        Measure.Regular η.totalVariation ∧
        (∀ s : Set PositiveReal, MeasurableSet s →
          η s = ∫ x in s, lognormalDensity σ x ∂positiveVolume) ∧
        (∀ z : ℝ,
          Integrable
              (fun x : PositiveReal => Real.rpow (x : ℝ) z) η.variation ∧
            (∫ᵛ x : PositiveReal, Real.rpow (x : ℝ) z ∂<•η) =
              lognormalConstant σ * Real.exp (σ ^ 2 * z ^ 2 / 2) *
                (Real.cos (2 * Real.pi * z) - 1) ∧
            lognormalConstant σ * Real.exp (σ ^ 2 * z ^ 2 / 2) *
                (Real.cos (2 * Real.pi * z) - 1) ≤ 0) ∧
        (∀ m : ℤ,
          (∫ᵛ x : PositiveReal,
              Real.rpow (x : ℝ) (m : ℝ) ∂<•η) = 0) ∧
        Summable (lognormalCarlemanTerm σ)

end
end MathlibPlus.Open.Analysis.O0342
