import Mathlib

open Asymptotics Filter MeasureTheory Topology

namespace MathlibPlus.Open.AnalyticNumberTheory.ReciprocalXi

/--
The Jacobi coefficients of the normalized reciprocal completed-xi measure obey the
relative Lambert-W law with relative error `O(1/n)`.  This is admitted claim 521.
-/
noncomputable def jacobiRelativeLambertLaw : Prop :=
  let xi : ℝ → ℝ := fun x =>
    let s : ℂ := (x : ℂ) + 1 / 2
    ((1 + s * (s - 1) * completedRiemannZeta₀ s) / 2).re
  let Q : ℝ → ℝ := fun x => Real.log (xi x)
  ∃ (W₀ : ℝ → ℝ) (Z : ℝ) (μ : Measure ℝ)
      (p : ℕ → Polynomial ℝ) (b error : ℕ → ℝ),
    (∀ x : ℝ, 0 ≤ x →
      0 ≤ W₀ x ∧ W₀ x * Real.exp (W₀ x) = x) ∧
    0 < Z ∧
    Z = ∫ x : ℝ, Real.exp (-Q x) ∧
    μ = Measure.withDensity volume
      (fun x => ENNReal.ofReal (Real.exp (-Q x) / Z)) ∧
    (∀ m n : ℕ,
      ∫ x : ℝ, (p m).eval x * (p n).eval x ∂μ = if m = n then 1 else 0) ∧
    (∀ n : ℕ, (p n).natDegree = n) ∧
    Polynomial.X * p 0 = Polynomial.C (b 1) * p 1 ∧
    (∀ n : ℕ,
      Polynomial.X * p (n + 1) =
        Polynomial.C (b (n + 2)) * p (n + 2) +
          Polynomial.C (b (n + 1)) * p n) ∧
    (∀ n : ℕ, 1 ≤ n → 0 < b n) ∧
    (∀ᶠ n : ℕ in atTop,
      b n =
        (Real.pi * (n : ℝ) / W₀ (2 * (n : ℝ) / Real.exp 1)) *
          (1 + error n)) ∧
    IsBigO atTop error (fun n : ℕ => ((n : ℝ)⁻¹))

end MathlibPlus.Open.AnalyticNumberTheory.ReciprocalXi
