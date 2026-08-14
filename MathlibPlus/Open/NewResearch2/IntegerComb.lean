import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.NewResearch2.R0203

private noncomputable def coefficientPairing
    (a : ℤ → ℂ) (φ : SchwartzMap ℝ ℂ) : ℂ :=
  ∑' n : ℤ, a n * φ (n : ℝ)

private noncomputable def FourierTest
    (φ : SchwartzMap ℝ ℂ) (x : ℝ) : ℂ :=
  ∫ y : ℝ,
    Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * (y : ℂ)) * φ y

private noncomputable def polynomiallyBounded (a : ℤ → ℂ) : Prop :=
  ∃ C : ℝ, ∃ k : ℕ, 0 ≤ C ∧
    ∀ n : ℤ, ‖a n‖ ≤ C * (1 + |(n : ℝ)|) ^ k

private noncomputable def FourierSelfDual (a : ℤ → ℂ) : Prop :=
  ∀ φ : SchwartzMap ℝ ℂ,
    coefficientPairing a φ =
      ∑' n : ℤ, a n * FourierTest φ (n : ℝ)

/-- Claim 18781: the integer Dirac comb, represented by its action on
Schwartz test functions, is tempered and Fourier self-dual. -/
def claim18781_integerDiracComb : Prop :=
  let comb : ℤ → ℂ := fun _ ↦ 1
  polynomiallyBounded comb ∧
    FourierSelfDual comb ∧
    (∀ φ : SchwartzMap ℝ ℂ,
      coefficientPairing comb φ = ∑' n : ℤ, φ (n : ℝ))

/-- Claim 18782: integer support makes multiplication by the unit character
invisible to the distribution. -/
def claim18782_integerSupportModulationInvariance : Prop :=
  ∀ a : ℤ → ℂ, polynomiallyBounded a →
    ∀ φ : SchwartzMap ℝ ℂ,
      (∑' n : ℤ,
        a n *
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
            φ (n : ℝ))) =
        ∑' n : ℤ, a n * φ (n : ℝ)

/-- Claim 18784: a tempered integer-supported Fourier-self-dual pure-point
measure has constant coefficients, hence is a scalar multiple of the comb. -/
def claim18784_exactSupportSelfDualCombRigidity : Prop :=
  ∀ a : ℤ → ℂ, polynomiallyBounded a → FourierSelfDual a →
    ∃ c : ℂ, ∀ n : ℤ, a n = c

/-- Claim 18785: in the positive cone the scalar is nonnegative and the comb
spans the only nonzero ray. -/
def claim18785_uniquePositiveExtremalRay : Prop :=
  ∀ b : ℤ → ℝ,
    polynomiallyBounded (fun n ↦ (b n : ℂ)) →
    (∀ n : ℤ, 0 ≤ b n) →
    FourierSelfDual (fun n ↦ (b n : ℂ)) →
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n : ℤ, b n = c

end MathlibPlus.Open.NewResearch2.R0203
