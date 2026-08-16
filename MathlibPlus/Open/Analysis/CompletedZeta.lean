import Mathlib

/-!
# Finite total-Loewner criterion for the Riemann hypothesis

This registry node records admitted claim 195 from source record `C-0013`.
The exact total family is built from the logarithmic derivative of the completed
Riemann xi function on `s = 1/2 + λ`. Quantifying over every injective finite rate
family also quantifies over every principal subfamily, so the negative-determinant
clause is the claimed finite principal-minor falsifier.
-/

namespace MathlibPlus.Open.Analysis.CompletedZeta

/-- Positive semidefiniteness of every finite total even prime-side Loewner section
is equivalent to RH, and a negative finite principal determinant refutes RH. -/
noncomputable def finiteLoewnerCriterion : Prop :=
  let xi : ℂ → ℂ := fun s =>
    (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s
  let X : ℝ → ℝ := fun lambda =>
    (xi (((1 / 2 : ℝ) + lambda : ℝ) : ℂ)).re
  let L : ℝ → ℝ := fun lambda => deriv X lambda / X lambda
  let totalEvenLoewner :
      (n : ℕ) → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ :=
    fun _ rates i j =>
      if i = j then
        2 * (L (rates i) / rates i - deriv L (rates i))
      else
        4 * (rates j * L (rates i) - rates i * L (rates j)) /
          (rates j ^ 2 - rates i ^ 2)
  (RiemannHypothesis ↔
      ∀ (n : ℕ) (rates : Fin n → ℝ),
        0 < n →
        (∀ i, 1 / 2 < rates i) →
        Function.Injective rates →
        Matrix.PosSemidef (totalEvenLoewner n rates)) ∧
    (∀ (n : ℕ) (rates : Fin n → ℝ),
      0 < n →
      (∀ i, 1 / 2 < rates i) →
      Function.Injective rates →
      Matrix.det (totalEvenLoewner n rates) < 0 →
      ¬RiemannHypothesis)

end MathlibPlus.Open.Analysis.CompletedZeta
