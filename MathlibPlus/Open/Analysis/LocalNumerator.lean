import Mathlib

namespace MathlibPlus.Open.Analysis.LocalNumerator

/-!
The local prime-factor classification from admitted claim 13775.  The complex
power is Mathlib's principal `Complex.cpow`; the displayed absolute square is
represented by the squared complex norm.  The `p = 2` `±`-family is written as
two explicit integer-parametrized alternatives.
-/
noncomputable def localNumeratorClassification : Prop :=
  let D : ℕ → ℝ → ℝ := fun p x =>
    (1 - (p : ℝ)⁻¹) *
      ‖(1 : ℂ) - (p : ℂ) ^ ((-1 : ℂ) + 2 * (x : ℂ) * Complex.I)‖ ^ 2
  let N : ℕ → ℝ → ℝ := fun p x =>
    1 - (1 + 2 * Real.cos (2 * x * Real.log (p : ℝ))) / (p : ℝ)
  (∀ (p : ℕ) (x : ℝ), p.Prime → 0 < D p x) ∧
    (∀ (p : ℕ) (x : ℝ), p.Prime → 5 ≤ p → 0 < N p x) ∧
    (∀ x : ℝ,
      0 ≤ N 3 x ∧
        (N 3 x = 0 ↔
          ∃ k : ℤ, x = (k : ℝ) * (Real.pi / Real.log 3))) ∧
    (∀ x : ℝ,
      Real.sign (N 2 x) =
          Real.sign ((1 / 2 : ℝ) - Real.cos (2 * x * Real.log 2)) ∧
        (N 2 x = 0 ↔
          ∃ k : ℤ,
            x = Real.pi * (6 * (k : ℝ) + 1) / (6 * Real.log 2) ∨
            x = Real.pi * (6 * (k : ℝ) - 1) / (6 * Real.log 2)))

end MathlibPlus.Open.Analysis.LocalNumerator
