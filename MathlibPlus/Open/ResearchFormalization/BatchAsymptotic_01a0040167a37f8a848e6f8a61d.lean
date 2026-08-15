import Mathlib

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_01a0040167a37f8a848e6f8a61d

/-! Fixed parabolic-ray polynomial absorption obstruction. -/

def claim60013 : Prop :=
  ∀ (C A : ℝ), 0 < C →
    ∀ k : ℕ, ∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m →
      let N : ℝ := (m : ℝ) ^ 2
      0 < (m : ℝ) ∧
        N ≥ (3 / (2 * Real.pi)) * N + A * Real.sqrt N ∧
        Real.exp ((3 / 2 : ℝ) * N - Real.pi * ((m : ℝ) - 1) ^ 2) >
          C * N ^ k * Real.exp ((3 / 2 : ℝ) * N - Real.pi * (m : ℝ) ^ 2)

/-! Nonvanishing finite forward gamma recurrence. -/

def gammaRecurrence (n : ℕ) (z : ℂ) : ℂ :=
  ∏ k ∈ Finset.range n, (z + (k : ℂ))

def claim60015 : Prop :=
  (∀ (n : ℕ) (z : ℂ) (σ : ℝ), 0 < σ → σ ≤ z.re →
    σ ^ n ≤ ‖gammaRecurrence n z‖) ∧
    (∀ (n : ℕ) (z : ℂ), 0 < z.re → gammaRecurrence n z ≠ 0) ∧
    (∀ (n : ℕ) (z : ℂ), 0 < z.re → z.re < 1 →
      gammaRecurrence n z ≠ 0)

/-! Exact closed benchmark budget equivalence. -/

def claim60017 : Prop :=
  ∀ (εt εy : ℝ), 0 ≤ εt → 0 ≤ εy →
    ((∀ (δt δy Λ : ℝ),
        |δt| ≤ εt → |δy| ≤ εy →
        Λ ≤ 1579 / 10000 + δt + (1 / 2) * (1 / 10 + δy) ^ 2 →
        Λ ≤ 163 / 1000) ↔
      εt + εy / 10 + εy ^ 2 / 2 ≤ 1 / 10000)


end MathlibPlus.Open.ResearchFormalization.Batch_01a0040167a37f8a848e6f8a61d
