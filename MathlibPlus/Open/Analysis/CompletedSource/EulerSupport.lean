import Mathlib

open Filter
open scoped BigOperators Topology

namespace MathlibPlus.Open.Analysis.CompletedSource

/--
Euler--von Mangoldt coefficients are excluded below the first inverse-Laplace atom.

This is admitted claim 327. The coefficient is the Taylor coefficient at zero of the
exact prime-power Cayley atom. The complete sequence includes the exact Dirichlet
weight from the completed-xi logarithmic derivative. "Up to a fixed polynomial
factor" is stated by explicit constants `C`, `k`, and `δ`; the matrix-index consequence
is uniform through `2n + c` for every fixed offset `c`, which is the literal `2n+O(1)`
assertion.
-/
noncomputable def eulerCoefficientSupportExclusion : Prop :=
  let IsPrimePower : ℕ → Prop := fun m =>
    ∃ p k : ℕ, Nat.Prime p ∧ 0 < k ∧ m = p ^ k
  let atom : ℕ → ℝ → ℂ → ℂ := fun m r s =>
    Complex.exp
      (-((Real.log (m : ℝ) * r : ℝ) : ℂ) * ((1 - s) / (1 + s)))
  let coeff : ℕ → ℝ → ℕ → ℂ := fun m r j =>
    iteratedDeriv j (atom m r) 0 / (Nat.factorial j : ℂ)
  let weightedCoeff : ℕ → ℝ → ℕ → ℂ := fun m r j =>
    ((ArithmeticFunction.vonMangoldt m * Real.log (m : ℝ) /
      Real.sqrt (m : ℝ) : ℝ) : ℂ) * coeff m r j
  let eulerCoeff : ℝ → ℕ → ℂ := fun r j =>
    ∑' m : ℕ, weightedCoeff m r j
  (∀ (m j : ℕ) (r ρ : ℝ), IsPrimePower m → 0 < r → 0 < ρ → ρ < 1 →
      ‖coeff m r j‖ ≤
        (ρ ^ j)⁻¹ * Real.exp
          (-Real.log (m : ℝ) * r * (1 - ρ) / (1 + ρ))) ∧
  (∀ (U : ℝ) (m : ℕ), IsPrimePower m → U < Real.log (m : ℝ) / 2 →
      ∃ ρ δ : ℝ,
        0 < ρ ∧ ρ < 1 ∧
        δ = Real.log (m : ℝ) * (1 - ρ) / (1 + ρ) + U * Real.log ρ ∧
        0 < δ ∧
        ∀ (r : ℝ), 0 < r → ∀ j : ℕ, (j : ℝ) / r ≤ U →
          ‖coeff m r j‖ ≤ Real.exp (-δ * r)) ∧
  (∀ (r : ℝ), 0 < r → ∀ j : ℕ,
      Summable (fun m : ℕ => weightedCoeff m r j)) ∧
  (∀ U : ℝ, U < Real.log 2 / 2 →
      ∃ (C : ℝ) (k : ℕ) (δ : ℝ),
        0 ≤ C ∧ 0 < δ ∧
        ∀ (r : ℝ), 1 ≤ r → ∀ j : ℕ, (j : ℝ) / r ≤ U →
          ‖eulerCoeff r j‖ ≤
            C * (1 + r) ^ k * Real.exp (-δ * r)) ∧
  (∀ (α : ℝ), α < Real.log 2 / 4 →
      ∀ (n : ℕ → ℕ) (r : ℕ → ℝ),
        Tendsto r atTop atTop →
        Tendsto (fun q => (n q : ℝ) / r q) atTop (𝓝 α) →
        ∀ c : ℕ,
          ∃ (C : ℝ) (k : ℕ) (δ : ℝ),
            0 ≤ C ∧ 0 < δ ∧
            ∀ᶠ q in atTop, ∀ j : ℕ, j ≤ 2 * n q + c →
              ‖eulerCoeff (r q) j‖ ≤
                C * (1 + r q) ^ k * Real.exp (-δ * r q)) ∧
  ((1 / 3 : ℝ) - 2 * (138806 / 1000000 : ℝ)) * Real.log 2 >
    (386230850970 / 10000000000000 : ℝ)

end MathlibPlus.Open.Analysis.CompletedSource
