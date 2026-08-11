import Mathlib

/-!
# Bernstein coefficient pattern for the connected-triple numerator

This registry node formalizes admitted claim 182. The rank-four determinant,
mixed logarithmic derivative, symmetry, and tensor Bernstein basis are all
spelled out, so the coefficient signs do not rely on an unstated numerator or
basis normalization.
-/

open scoped BigOperators

namespace MathlibPlus.Open.ConnectedTriple

/-- The symmetric numerator defined by the rank-four mixed logarithmic
derivative has a degree-seven tensor Bernstein representation on
`[0,1/4] × [0,1/9] × [0,1/16]` with 508 positive coefficients and exactly
four negative coefficients, at `(3,0,0)`, `(4,0,0)`, `(5,0,0)`, and
`(6,0,0)`. -/
def bernsteinCoefficientPattern : Prop :=
  let moment : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℕ → ℝ :=
    fun r s t a b c j => 1 + a * r ^ j + b * s ^ j + c * t ^ j
  let coefficient : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℕ → ℝ :=
    fun r s t a b c j => moment r s t a b c j / Nat.factorial (2 * j)
  let determinant : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ :=
    fun r s t a b c => Matrix.det (fun i j : Fin 4 =>
      ∑ x ∈ Finset.range (min i.1 j.1 + 1),
        (i.1 + j.1 + 1 - 2 * x : ℕ) * coefficient r s t a b c x *
          coefficient r s t a b c (i.1 + j.1 + 1 - x))
  let mixedLogDerivative : ℝ → ℝ → ℝ → ℝ := fun r s t =>
    deriv (fun a => deriv (fun b =>
      deriv (fun c => Real.log (determinant r s t a b c)) 0) 0) 0
  let basis : ℝ → ℝ → Fin 8 → ℝ := fun upper x i =>
    (Nat.choose 7 i.1 : ℝ) * (x / upper) ^ i.1 *
      (1 - x / upper) ^ (7 - i.1)
  let isNegativeIndex : Fin 8 → Fin 8 → Fin 8 → Prop := fun i j k =>
    j = 0 ∧ k = 0 ∧ (i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6)
  ∃ (P : ℝ → ℝ → ℝ → ℝ) (β : Fin 8 → Fin 8 → Fin 8 → ℝ),
    (∀ r s t, mixedLogDerivative r s t = P r s t / (2 : ℝ) ^ 29) ∧
    (∀ r s t, P r s t = P s r t ∧ P r s t = P r t s) ∧
    (∀ r s t : ℝ,
      0 ≤ r → r ≤ 1 / 4 →
      0 ≤ s → s ≤ 1 / 9 →
      0 ≤ t → t ≤ 1 / 16 →
      P r s t =
        ∑ i, ∑ j, ∑ k,
          β i j k * basis (1 / 4) r i * basis (1 / 9) s j *
            basis (1 / 16) t k) ∧
    (∀ i j k, β i j k < 0 ↔ isNegativeIndex i j k) ∧
    (∀ i j k, 0 < β i j k ↔ ¬ isNegativeIndex i j k) ∧
    (Finset.univ.filter (fun x : Fin 8 × Fin 8 × Fin 8 =>
      0 < β x.1 x.2.1 x.2.2)).card = 508 ∧
    (Finset.univ.filter (fun x : Fin 8 × Fin 8 × Fin 8 =>
      β x.1 x.2.1 x.2.2 < 0)).card = 4

end MathlibPlus.Open.ConnectedTriple
