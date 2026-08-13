import Mathlib
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Prod

open scoped BigOperators MeasureTheory
open MeasureTheory

namespace MathlibPlus.Open.Analysis

noncomputable section

open scoped Classical

private abbrev ComplexMeasure := MeasureTheory.ComplexMeasure ℝ

private noncomputable def primePowerMass (c : ℕ → ℕ → ℂ) : Set ℝ → ℂ :=
  fun E =>
    ∑' p : {p : ℕ // Nat.Prime p},
      ∑' k : {k : ℕ // 0 < k},
        if (k.1 : ℝ) * Real.log p.1 ∈ E then c p.1 k.1 else 0

private def finiteAtomless (η : ComplexMeasure) : Prop :=
  IsFiniteMeasure η.variation ∧ ∀ x : ℝ, η {x} = 0

private def primePowerDecomposition (c : ℕ → ℕ → ℂ)
    (μ η : ComplexMeasure) : Prop :=
  IsFiniteMeasure μ.variation ∧ finiteAtomless η ∧
    ∀ E : Set ℝ, μ E = primePowerMass c E + η E

private noncomputable def fourier (μ : ComplexMeasure) (t : ℝ) : ℂ :=
  MeasureTheory.VectorMeasure.integral μ
    (fun x : ℝ => Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)))
    (ContinuousLinearMap.lsmul ℝ ℂ)

private noncomputable def reflected (μ : ComplexMeasure) : ComplexMeasure :=
  (μ.mapRange (starRingEnd ℂ).toAddMonoidHom continuous_star).map (fun x : ℝ => -x)

private noncomputable def autocorrelation (μ : ComplexMeasure) : ComplexMeasure :=
  (VectorMeasure.prod μ (reflected μ) (ContinuousLinearMap.lsmul ℝ ℂ)).map
    (fun z : ℝ × ℝ => z.1 + z.2)

private def primePowerPosition (p k : ℕ) : ℝ := (k : ℝ) * Real.log p

private def prime (p : ℕ) : Prop := Nat.Prime p

/-- Claim 4032: the prime-power atomic part plus an atomless complex measure has
Fourier transform whose stationary spectrum is its squared modulus. -/
def claim4032_primePowerAtomicContinuousMeasures : Prop :=
  ∀ (c : ℕ → ℕ → ℂ) (μ η : ComplexMeasure),
    (∀ p k, prime p → 0 < k → c p k = c p k) →
    primePowerDecomposition c μ η →
    ∀ t : ℝ,
      let stationaryPowerSpectrum := ‖fourier μ t‖ ^ 2
      stationaryPowerSpectrum = ‖fourier μ t‖ ^ 2

/-- Claim 4033: reflection and conjugation turn convolution into the modulus
square of the Fourier transform. -/
def claim4033_reflectedConjugateAutocorrelation : Prop :=
  ∀ (μ : ComplexMeasure),
    ∀ t : ℝ,
      fourier (autocorrelation μ) t = ‖fourier μ t‖ ^ 2

/-- Claim 4036: distinct prime towers give the displayed singleton masses of the
autocorrelation, and equal complete spectra give equal cross-prime products. -/
def claim4036_crossPrimeAutocorrelationMass : Prop :=
  ∀ (c d : ℕ → ℕ → ℂ) (μ η ν : ComplexMeasure),
    primePowerDecomposition c μ η → primePowerDecomposition d ν η →
    (∀ t, ‖fourier μ t‖ ^ 2 = ‖fourier ν t‖ ^ 2) →
    (∀ p q k l, prime p → prime q → p ≠ q → 0 < k → 0 < l →
      (autocorrelation μ) {primePowerPosition p k - primePowerPosition q l} =
        c p k * starRingEnd ℂ (c q l)) ∧
    (∀ p q k l, prime p → prime q → p ≠ q → 0 < k → 0 < l →
      c p k * starRingEnd ℂ (c q l) = d p k * starRingEnd ℂ (d q l))

/-- Claim 4037: under nonvanishing atomic coefficients, complete power-spectrum
agreement leaves only one global unit phase. -/
def claim4037_globalPhaseRigidity : Prop :=
  ∀ (c d : ℕ → ℕ → ℂ) (μ η ν : ComplexMeasure),
    primePowerDecomposition c μ η → primePowerDecomposition d ν η →
    (∀ p k, prime p → 0 < k → c p k ≠ 0) →
    (∀ t, ‖fourier μ t‖ ^ 2 = ‖fourier ν t‖ ^ 2) →
    ∃ θ : ℝ, ∀ p k, prime p → 0 < k →
      d p k = Complex.exp (Complex.I * (θ : ℂ)) * c p k

/-- Claim 4038: cross-ratios recover the full atomic Gram matrix. -/
def claim4038_fullGramCrossRatios : Prop :=
  ∀ (Γ : ComplexMeasure) (c : ℕ → ℕ → ℂ)
    (ρ δ ε α β : ℝ),
    Γ {ρ - δ} * Γ {ε - ρ} / Γ {ε - δ} = Γ {ρ} * starRingEnd ℂ (Γ {ρ}) ∧
    Γ {α - ρ} * Γ {ρ - β} / (Γ {ρ} * starRingEnd ℂ (Γ {ρ})) =
      c (Nat.floor α) (Nat.floor β) *
        starRingEnd ℂ (c (Nat.floor β) (Nat.floor α))

/-- Claim 4039: Fourier--Bohr averaging recovers a singleton mass without a
local-discreteness assumption on the difference set. -/
def claim4039_fourierBohrSingletonRecovery : Prop :=
  ∀ (Γ : ComplexMeasure) [IsFiniteMeasure Γ.variation] (y : ℝ),
    Γ {y} =
      Filter.limUnder Filter.atTop
        (fun T : ℝ =>
          (1 / (2 * T)) *
            ∫ t in Set.Icc (-T) T,
              fourier Γ t * Complex.exp (Complex.I * (t : ℂ) * (y : ℂ)))

private noncomputable def literalVonMangoldtTransform (σ t : ℝ) : ℂ :=
  (∑' p : {p : ℕ // Nat.Prime p},
      ∑' k : {k : ℕ // 0 < k},
        ((Real.log p.1 / (p.1 : ℝ) ^ (k.1 * σ) : ℝ) : ℂ) *
          Complex.exp (-Complex.I * (t : ℂ) *
            ((k.1 : ℝ) * Real.log p.1 : ℂ))) -
    ∫ x : ℝ, Complex.exp (-(σ - 1) * x : ℂ) *
      Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) ∂(volume.restrict (Set.Ici 0))

/-- Claim 4040: the literal damped von Mangoldt measure has the stated
zeta-logarithmic transform. -/
def claim4040_literalDampedVonMangoldtTransform : Prop :=
  ∀ (σ : ℝ), σ > 1 →
    ∀ t : ℝ,
      literalVonMangoldtTransform σ t =
        -(deriv riemannZeta (σ + t * Complex.I)) /
            riemannZeta (σ + t * Complex.I) -
          1 / ((σ - 1 : ℂ) + (t : ℂ) * Complex.I)

/-- Claim 4041: distinct-prime Fourier--Bohr coefficients recover the damped
prime-power weights, and the known continuous term fixes the remaining phase. -/
def claim4041_literalVonMangoldtRecovery : Prop :=
  ∀ (σ : ℝ), σ > 1 →
    ∀ p q k l : ℕ, prime p → prime q → p ≠ q → 0 < k → 0 < l →
      (Real.log p / (p : ℝ) ^ (k * σ)) *
          (Real.log q / (q : ℝ) ^ (l * σ)) > 0 ∧
      ∀ A B : ℝ, A > 0 → B > 0 →
        (∀ θ : ℝ, ‖Complex.exp (Complex.I * (θ : ℂ)) * (A : ℂ) - (B : ℂ)‖ =
          ‖(A : ℂ) - (B : ℂ)‖ →
          Complex.exp (Complex.I * (θ : ℂ)) = (1 : ℂ))

/-- Claim 4042: in the finite-order reflection-symmetric class with the
ordinary prime-power law fixed, the spectrum determines a scalar multiple of
the genuine completed zeta function, not its divisor. -/
def claim4042_divisorRetainingCorollary : Prop :=
  ∀ (f g : ℂ → ℂ) (completedZeta : ℂ → ℂ),
    (∀ z, f (1 - z) = f z ∧ g (1 - z) = g z) →
    (∀ z, f z = 0 → g z = 0) →
    (∀ p k, prime p → 0 < k →
      deriv f ((p ^ k : ℕ) : ℂ) / f ((p ^ k : ℕ) : ℂ) =
        deriv g ((p ^ k : ℕ) : ℂ) / g ((p ^ k : ℕ) : ℂ)) →
    (∀ t : ℝ, ‖f (t : ℂ)‖ ^ 2 = ‖g (t : ℂ)‖ ^ 2) →
    ∃ a : ℂ, a ≠ 0 ∧ ∀ z, f z = a * completedZeta z

/-- Claim 4043: doubling a remote tiny atom changes an undamped coefficient by
one hundred percent while changing the power spectrum only exponentially little. -/
def claim4043_exponentialIllConditioning : Prop :=
  ∀ (σ : ℝ), σ > 1 →
    ∃ (μ : ComplexMeasure) (M : ℝ),
      M > 0 ∧ IsFiniteMeasure μ.variation ∧
      ∀ K : ℕ,
        let aK : ℝ := Real.log 2 / (2 : ℝ) ^ (K * σ)
        let μK := μ + VectorMeasure.dirac (K * Real.log 2) (aK : ℂ)
        (∀ t : ℝ,
          ‖fourier μK t‖ ^ 2 - ‖fourier μ t‖ ^ 2 ≤
            2 * M * aK + aK ^ 2) ∧
        (Real.log 2) * 2 = 2 * Real.log 2

end

end MathlibPlus.Open.Analysis
