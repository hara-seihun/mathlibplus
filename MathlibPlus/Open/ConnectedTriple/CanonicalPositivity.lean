import Mathlib

/-!
# Canonical three-shell positivity

This registry node formalizes admitted claim 185 without replacing the
canonical integer-shell quantifiers by a finite scan or by arbitrary real
supports. The determinant normalization and numerator symmetry are explicit.
-/

open scoped BigOperators

namespace MathlibPlus.Open.ConnectedTriple

/-- The symmetric rank-four mixed-log-derivative numerator is positive on
every strictly ordered canonical triple of integer shells. -/
def everyCanonicalThreeShellNumeratorPositive : Prop :=
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
  ∃ P : ℝ → ℝ → ℝ → ℝ,
    (∀ r s t, mixedLogDerivative r s t = P r s t / (2 : ℝ) ^ 29) ∧
    (∀ r s t, P r s t = P s r t ∧ P r s t = P r t s) ∧
    ∀ i j k : ℤ,
      2 ≤ i → i < j → j < k →
        0 < P ((i : ℝ)⁻¹ ^ 2) ((j : ℝ)⁻¹ ^ 2) ((k : ℝ)⁻¹ ^ 2)

end MathlibPlus.Open.ConnectedTriple
