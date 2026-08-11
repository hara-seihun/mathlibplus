import Mathlib

/-!
# Stieltjes moment-ratio constraints

Formal statement of admitted claim 160.  A nonzero positive measure carried by
`(0, ∞)` has the two Hankel inequalities that constrain the scale-free ratios
`R = m₁² / (m₀m₂)` and `S = m₁m₃ / m₂²`.
-/

namespace MathlibPlus.Open.Analysis.MomentGeometry

open MeasureTheory Set

/-- For a nonzero positive measure carried by `(0, ∞)` with finite moments
through degree three and nonzero moments used by the ratios, Stieltjes/Hankel
positivity forces `0 < R ≤ 1` and `1 ≤ S`.

The support condition is stated measure-theoretically as `μ (Iic 0) = 0`.
The explicit nonvanishing assumptions expose the source phrase "nonzero
relevant moments" rather than silently deriving or strengthening it. -/
def stieltjesRatioConstraints : Prop :=
  ∀ μ : Measure ℝ,
    μ ≠ 0 →
    μ (Iic (0 : ℝ)) = 0 →
    (∀ j : Fin 4, Integrable (fun x : ℝ => x ^ (j : ℕ)) μ) →
    let m : ℕ → ℝ := fun j => ∫ x : ℝ, x ^ j ∂μ
    m 0 ≠ 0 →
    m 1 ≠ 0 →
    m 2 ≠ 0 →
    0 < m 1 ^ 2 / (m 0 * m 2) ∧
      m 1 ^ 2 / (m 0 * m 2) ≤ 1 ∧
      1 ≤ m 1 * m 3 / m 2 ^ 2

end MathlibPlus.Open.Analysis.MomentGeometry
