import Mathlib
import MathlibPlus.Algebra.Claim19020EulerLikeFactor

open MeasureTheory
open scoped BigOperators

namespace MathlibPlus.Open.FormalizationBatch.R0228Claim19025

private noncomputable def complexLocalFactor
    (q ℓ : ℝ) (z : ℂ) : ℂ :=
  (1 + (q : ℂ) * Complex.exp ((ℓ : ℂ) * z)) *
    (1 + (q : ℂ) * Complex.exp (-((ℓ : ℂ) * z)))

private noncomputable def realLocalFactor
    (q ℓ : ℝ) : ℝ → ℝ :=
  MathlibPlus.Algebra.Claim19020.euler_like_factor_claim19020 q ℓ

private noncomputable def localZeroPoint
    (q ℓ : ℝ) (k ε : ℤ) : ℂ :=
  ((ε : ℂ) * (Real.log (1 / q) : ℂ) / (ℓ : ℂ)) +
    (((2 * k + 1 : ℤ) : ℂ) * (Real.pi : ℂ) * Complex.I / (ℓ : ℂ))

private def atomicLocation
    (ℓ : Fin n → ℝ) (j : Fin n) (v : Fin 3) : ℝ :=
  if v = 0 then 0 else if v = 1 then ℓ j else -ℓ j

private def atomicWeight
    (q : Fin n → ℝ) (j : Fin n) (v : Fin 3) : ℝ :=
  if v = 0 then 1 + (q j) ^ 2 else q j

private noncomputable def finiteConvolutionMeasure
    (q ℓ : Fin n → ℝ) : Measure ℝ :=
  ∑ s : Fin n → Fin 3,
    ENNReal.ofReal (∏ j, atomicWeight q j (s j)) •
      Measure.dirac (∑ j, atomicLocation ℓ j (s j))

/-- Claim 19025: finite products retain the exact factor symmetry, positive
finite convolution-measure transform, imaginary-axis strict positivity, every
local zero, and the explicit nonempty-product off-axis zero conclusion. -/
def claim19025_finiteProductSoftProperties : Prop :=
  ∀ (n : ℕ) (q ℓ : Fin n → ℝ),
    (∀ j, 0 < q j ∧ q j < 1 ∧ 0 < ℓ j) →
      let F : ℂ → ℂ := fun z =>
        ∏ j, complexLocalFactor (q j) (ℓ j) z
      let μ : Measure ℝ := finiteConvolutionMeasure q ℓ
      (∀ j : Fin n, ∀ x : ℝ,
        complexLocalFactor (q j) (ℓ j) (x : ℂ) =
          (realLocalFactor (q j) (ℓ j) x : ℂ)) ∧
      (∀ z : ℂ, F (-z) = F z) ∧
      IsFiniteMeasure μ ∧
      Measure.map Neg.neg μ = μ ∧
      (∀ z : ℂ,
        ∫ x : ℝ, Complex.exp (z * (x : ℂ)) ∂μ = F z) ∧
      (∀ t : ℝ,
        (F ((t : ℂ) * Complex.I)).im = 0 ∧
          0 < (F ((t : ℂ) * Complex.I)).re) ∧
      (∀ z : ℂ, ∀ j : Fin n,
        complexLocalFactor (q j) (ℓ j) z = 0 → F z = 0) ∧
      (n ≠ 0 →
        ∃ j : Fin n, ∃ k ε : ℤ,
          (ε = -1 ∨ ε = 1) ∧
          complexLocalFactor (q j) (ℓ j)
              (localZeroPoint (q j) (ℓ j) k ε) = 0 ∧
          F (localZeroPoint (q j) (ℓ j) k ε) = 0 ∧
          (localZeroPoint (q j) (ℓ j) k ε).re ≠ 0)

end MathlibPlus.Open.FormalizationBatch.R0228Claim19025
