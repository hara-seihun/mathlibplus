import Mathlib

/-!
# Scaled-edge residual decomposition

This registry node formalizes admitted claim 183. The rank-four determinant,
mixed logarithmic derivative, numerator symmetry, global residual identity,
and degree-seven tensor Bernstein certificate are retained explicitly.
-/

open scoped BigOperators

namespace MathlibPlus.Open.ConnectedTriple

/-- The symmetric connected-triple numerator is its scaled degenerate edge
plus a residual whose 64 `t`-face Bernstein coefficients vanish and whose
other 448 coefficients are strictly positive. The residual is strictly
positive in the canonical box whenever `t > 0`. -/
def scaledEdgeResidualDecomposition : Prop :=
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
  ∃ (P R : ℝ → ℝ → ℝ → ℝ) (β : Fin 8 → Fin 8 → Fin 8 → ℝ),
    (∀ r s t, mixedLogDerivative r s t = P r s t / (2 : ℝ) ^ 29) ∧
    (∀ r s t, P r s t = P s r t ∧ P r s t = P r t s) ∧
    (∀ r s t : ℝ,
      P r s t = (1 - 16 * t) ^ 7 * P r s 0 + R r s t) ∧
    (∀ r s t : ℝ,
      0 ≤ r → r ≤ 1 / 4 →
      0 ≤ s → s ≤ 1 / 9 →
      0 ≤ t → t ≤ 1 / 16 →
      R r s t =
        ∑ i, ∑ j, ∑ k,
          β i j k * basis (1 / 4) r i * basis (1 / 9) s j *
            basis (1 / 16) t k) ∧
    (∀ i j k, β i j k = 0 ↔ k = 0) ∧
    (∀ i j k, 0 < β i j k ↔ k ≠ 0) ∧
    (Finset.univ.filter (fun x : Fin 8 × Fin 8 × Fin 8 =>
      β x.1 x.2.1 x.2.2 = 0)).card = 64 ∧
    (Finset.univ.filter (fun x : Fin 8 × Fin 8 × Fin 8 =>
      0 < β x.1 x.2.1 x.2.2)).card = 448 ∧
    ∀ r s t : ℝ,
      0 ≤ r → r ≤ 1 / 4 →
      0 ≤ s → s ≤ 1 / 9 →
      0 < t → t ≤ 1 / 16 →
      0 < R r s t

end MathlibPlus.Open.ConnectedTriple
