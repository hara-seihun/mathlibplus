import Mathlib

namespace MathlibPlus.Open

open scoped BigOperators Topology
open Filter

noncomputable def gaugedHeatDeterminant (γ : ℝ) (n m : ℕ) : ℝ :=
  Real.exp (-(γ * (m : ℝ) * ((m : ℝ) ^ 2 - 1)) / (6 * (n : ℝ))) *
    Finset.prod (Finset.Icc 1 (m - 1))
      (fun d => (2 * Real.sinh (γ * (d : ℝ) / (n : ℝ))) ^ (m - d))

noncomputable def gaugedCrossRatio (γ : ℝ) (n m : ℕ) : ℝ :=
  gaugedHeatDeterminant γ n m * gaugedHeatDeterminant γ n (m - 2) /
    (gaugedHeatDeterminant γ n (m - 1)) ^ 2

noncomputable def heatCrossRatioReserve (γ : ℝ) (n m : ℕ) : ℝ :=
  1 - Real.exp (-2 * γ * ((m - 1 : ℕ) : ℝ) / (n : ℝ))

noncomputable def squareRootCrossRatio (γ x : ℝ) (n : ℕ) : ℝ :=
  gaugedCrossRatio γ n (Nat.floor (x * Real.sqrt (n : ℝ)))

def exactGaugedCrossRatioAndSquareRootReserve : Prop :=
  (∀ (γ : ℝ) (n m : ℕ),
      0 < n → 2 ≤ m →
        gaugedCrossRatio γ n m = heatCrossRatioReserve γ n m) ∧
    (∀ (γ x : ℝ),
      0 < γ → 0 < x →
        Filter.Tendsto
            (fun n : ℕ =>
              squareRootCrossRatio γ x n /
                (2 * γ * x / Real.sqrt (n : ℝ)))
            atTop (𝓝 1) ∧
          (∀ᶠ n : ℕ in atTop, 0 < squareRootCrossRatio γ x n))

end MathlibPlus.Open
