import Mathlib

open Filter Topology
open scoped BigOperators Topology

namespace MathlibPlus.Open.Analysis.Cayley

/-- The exact Cayley coefficients of the archimedean completed-source terms,
including their one-component and summed scaling limits.

Here `ψInf` sums the pole component `(a, λ) = (-1, -1)` and the gamma
components `(a, λ) = (1, 5 + 4k)`.  "Locally uniformly, including first and
second differences" is expressed by uniform convergence on every compact
subset of `(0, ∞)`, with discrete differences scaled as derivatives.
-/
def archimedeanCoefficientFormula : Prop :=
  let zMap : ℝ → ℝ := fun s ↦ (1 + s) / (1 - s)
  let component : ℝ → ℝ → ℝ → ℝ → ℝ := fun a lam r s ↦
    4 * a / (2 * r / (zMap s) + lam) ^ 2
  let ψ : ℝ → ℝ → ℝ → ℕ → ℝ := fun a lam r j ↦
    iteratedDeriv j (component a lam r) 0 / (Nat.factorial j : ℝ)
  let q : ℝ → ℝ → ℝ := fun lam r ↦ (2 * r - lam) / (2 * r + lam)
  let dInf : ℝ → ℝ := fun u ↦
    if u = 0 then 1 / 4
    else -u * Real.exp u + u * Real.exp (-5 * u) / (1 - Real.exp (-4 * u))
  let ψInf : ℝ → ℕ → ℝ := fun r j ↦
    ψ (-1) (-1) r j + ∑' k : ℕ, ψ 1 (5 + 4 * k) r j
  (∀ (a lam r : ℝ) (j : ℕ), 2 ≤ j → 2 * r + lam ≠ 0 →
      ψ a lam r j =
        4 * a * (q lam r) ^ (j - 2) / (2 * r + lam) ^ 2 *
          ((j : ℝ) * (1 + q lam r) ^ 2 + (q lam r) ^ 2 - 1)) ∧
  (∀ (a lam u : ℝ), 0 < u →
      Tendsto (fun r : ℝ ↦ r * ψ a lam r ⌊r * u⌋₊) atTop
        (𝓝 (4 * a * u * Real.exp (-lam * u)))) ∧
  (∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioi 0 →
      TendstoUniformlyOn
        (fun r u ↦ r * ψInf r ⌊r * u⌋₊)
        (fun u ↦ 4 * dInf u) atTop K) ∧
  (∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioi 0 →
      TendstoUniformlyOn
        (fun r u ↦ r ^ 2 *
          (ψInf r (⌊r * u⌋₊ + 1) - ψInf r ⌊r * u⌋₊))
        (fun u ↦ 4 * deriv dInf u) atTop K) ∧
  (∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioi 0 →
      TendstoUniformlyOn
        (fun r u ↦ r ^ 3 *
          (ψInf r (⌊r * u⌋₊ + 2) - 2 * ψInf r (⌊r * u⌋₊ + 1) +
            ψInf r ⌊r * u⌋₊))
        (fun u ↦ 4 * iteratedDeriv 2 dInf u) atTop K) ∧
  Tendsto (fun r : ℝ ↦ r * ψInf r 0) atTop (𝓝 (2 * dInf 0)) ∧
  Tendsto (fun r : ℝ ↦ r * ψInf r 1) atTop (𝓝 (4 * dInf 0))

end MathlibPlus.Open.Analysis.Cayley
