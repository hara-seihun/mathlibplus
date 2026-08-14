import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Claim 2638: shifted Euler operator and logarithmic unitary conjugation. -/
def claim2638_shiftedEulerOperatorAndLogarithmicUnitaryConjugation : Prop :=
  let D : (ℝ → ℂ) → ℝ → ℂ :=
    fun f x => (x : ℂ) * deriv f x + (1 / 2 : ℂ) * f x
  let Z : (ℝ → ℂ) → ℝ → ℂ :=
    fun f x => -D (D f) x
  let U : (ℝ → ℂ) → ℝ → ℂ :=
    fun f y => (Real.exp (y / 2) : ℂ) * f (Real.exp y)
  let Uinv : (ℝ → ℂ) → ℝ → ℂ :=
    fun g x =>
      if 0 < x then
        (Real.exp (-(Real.log x) / 2) : ℂ) * g (Real.log x)
      else 0
  (∀ f : ℝ → ℂ, ContDiffOn ℝ 2 f (Set.Ioi 0) →
      ∀ y : ℝ, U (Z f) y = -deriv (fun t : ℝ => deriv (U f) t) y) ∧
    (∀ f : ℝ → ℂ, ∀ x : ℝ, 0 < x → Uinv (U f) x = f x) ∧
    (∀ g : ℝ → ℂ, ∀ y : ℝ, U (Uinv g) y = g y) ∧
    (∀ f : ℝ → ℂ, MeasureTheory.IntegrableOn (fun x : ℝ => ‖f x‖ ^ 2) (Set.Ioi 0) →
      (∫ x in Set.Ioi 0, ‖f x‖ ^ 2) = ∫ y : ℝ, ‖U f y‖ ^ 2)

end MathlibPlus.Open.Analysis
