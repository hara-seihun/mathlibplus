import Mathlib
import MathlibPlus.Analysis.Claim13734

noncomputable section

open scoped BigOperators
open Filter Topology

namespace MathlibPlus.Open.Analysis.Claim13735

def rho (τ : ℝ) : ℂ := (1 / 2 : ℂ) + (τ : ℂ) * Complex.I

def normalizedFactor (τ : ℝ) (s : ℂ) : ℂ :=
  s * (1 - s) / (rho τ * (1 - rho τ))

def normalizedFactorsUnbounded : Prop :=
  ∀ τ : ℝ, ∀ B : ℝ, ∃ s : ℂ,
    0 < s.re ∧ s.re < 1 ∧ B < ‖normalizedFactor τ s‖

def unweightedProductDifferenceBound : Prop :=
  ∀ (N : ℕ) (z w : ℕ → ℂ),
    ‖(∏ k ∈ Finset.range N, z k) - ∏ k ∈ Finset.range N, w k‖ ≤
      ∑ k ∈ Finset.range N, ‖z k - w k‖

def pointwiseFactorConvergenceControlsProducts : Prop :=
  ∀ (a : ℕ → ℕ → ℂ),
    (∀ k : ℕ, Tendsto (fun N : ℕ => a N k) atTop (𝓝 (1 : ℂ))) →
      Tendsto (fun N : ℕ => ∏ k ∈ Finset.range (N + 1), a N k)
        atTop (𝓝 (1 : ℂ))

def weightedProductDifferenceBound : Prop :=
  ∀ (N : ℕ) (z w : ℕ → ℂ),
    ‖(∏ k ∈ Finset.range N, z k) - ∏ k ∈ Finset.range N, w k‖ ≤
      ∑ k ∈ Finset.range N,
        (‖z k - w k‖ * ∏ j ∈ Finset.range k, ‖w j‖) *
          ∏ j ∈ Finset.Ico (k + 1) N, ‖z j‖

def cannotDiscardMultiplicativeWeights : Prop :=
  weightedProductDifferenceBound ∧
    ¬ unweightedProductDifferenceBound ∧
    ¬ pointwiseFactorConvergenceControlsProducts

def claim13735 : Prop :=
  normalizedFactorsUnbounded ∧ cannotDiscardMultiplicativeWeights

end MathlibPlus.Open.Analysis.Claim13735
