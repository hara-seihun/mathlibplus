import Mathlib

/-!
# Generic GHS--Jensen Jacobi lower bound

Statement-fidelity formalization of admitted claim 425.  The probability law
`pPrev ^ 2 dμ` is represented without introducing a second measure: its unit
mass, support in the virial variable, and required integrability are stated
explicitly.  The hypotheses retain both orthonormality and the two exact
integration-by-parts identities used in the source.
-/

open MeasureTheory

namespace MathlibPlus.Open.Analysis.Jacobi

/--
Under the orthonormality, Jacobi derivative, virial, and virial-variable
concavity hypotheses of the GHS--Jensen argument, the positive Jacobi
coefficient has the claimed lower bound at every positive virial scale.
-/
def genericGHSJensenLowerBound : Prop :=
  ∀ (n : ℕ) (μ : Measure ℝ) (p pPrev q φ : ℝ → ℝ) (a b : ℝ),
    1 ≤ n →
    Integrable (fun x => p x ^ 2) μ →
    Integrable (fun x => pPrev x ^ 2) μ →
    Integrable (fun x => p x * pPrev x) μ →
    Integrable (fun x => q x * p x * pPrev x) μ →
    Integrable (fun x => x * q x * pPrev x ^ 2) μ →
    Integrable (fun x => q x ^ 2 * pPrev x ^ 2) μ →
    (∫ x, p x ^ 2 ∂μ) = 1 →
    (∫ x, pPrev x ^ 2 ∂μ) = 1 →
    (∫ x, p x * pPrev x ∂μ) = 0 →
    (n : ℝ) / b = ∫ x, q x * p x * pPrev x ∂μ →
    (∫ x, x * q x * pPrev x ^ 2 ∂μ) = 2 * (n : ℝ) - 1 →
    ConcaveOn ℝ (Set.Ici 0) φ →
    (∀ x : ℝ, 0 ≤ x * q x) →
    (∀ x : ℝ, φ (x * q x) = q x ^ 2) →
    0 < a →
    a * q a = 2 * (n : ℝ) - 1 →
    0 < b →
    b ≥ (n : ℝ) / q a ∧
      (n : ℝ) / q a = (n : ℝ) * a / (2 * (n : ℝ) - 1)

end MathlibPlus.Open.Analysis.Jacobi
