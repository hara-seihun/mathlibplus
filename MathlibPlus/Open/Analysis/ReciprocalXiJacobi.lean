import Mathlib

/-!
# Jacobi derivative and virial identities for the reciprocal-xi weight

This registry node formalizes admitted claim 424.  The reciprocal completed-xi
probability measure and the conventional degree-indexed, positive-leading-coefficient
orthonormal Jacobi recurrence are inlined.
-/

open MeasureTheory

namespace MathlibPlus.Open.Analysis.ReciprocalXi

/-- For every degree-indexed orthonormal-polynomial sequence satisfying the positive
Jacobi recurrence for the reciprocal-xi probability measure, the derivative
coefficient and the two integration-by-parts/virial identities hold at every
positive index.  The coefficient of `p_(n-1)` in `p_n'` is expressed by its
orthonormal inner product. -/
noncomputable def jacobiDerivativeAndVirialIdentities : Prop :=
  let xi : ℝ → ℝ := fun s =>
    (((1 : ℂ) + (s : ℂ) * ((s : ℂ) - 1) * completedRiemannZeta₀ (s : ℂ)) / 2).re
  let Q : ℝ → ℝ := fun x => Real.log (xi (1 / 2 + x))
  let Z : ℝ := ∫ x : ℝ, Real.exp (-Q x)
  let μ : Measure ℝ :=
    (ENNReal.ofReal Z⁻¹) •
      Measure.withDensity MeasureTheory.volume
        (fun x : ℝ => ENNReal.ofReal (Real.exp (-Q x)))
  ∀ (p : ℕ → Polynomial ℝ) (b : ℕ → ℝ),
    (∀ n : ℕ, (p n).natDegree = n ∧ 0 < (p n).leadingCoeff) →
    (∀ m n : ℕ,
      ∫ x : ℝ, (p m).eval x * (p n).eval x ∂μ = if m = n then 1 else 0) →
    (∀ n : ℕ, 1 ≤ n → 0 < b n) →
    (∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      x * (p n).eval x =
        b (n + 1) * (p (n + 1)).eval x + b n * (p (n - 1)).eval x) →
    ∀ n : ℕ, 1 ≤ n →
      (∫ x : ℝ, (p n).derivative.eval x * (p (n - 1)).eval x ∂μ =
        (n : ℝ) / b n) ∧
      (n : ℝ) / b n =
        ∫ x : ℝ, deriv Q x * (p n).eval x * (p (n - 1)).eval x ∂μ ∧
      (∫ x : ℝ, x * deriv Q x * ((p (n - 1)).eval x) ^ 2 ∂μ =
        2 * (n : ℝ) - 1)

end MathlibPlus.Open.Analysis.ReciprocalXi
