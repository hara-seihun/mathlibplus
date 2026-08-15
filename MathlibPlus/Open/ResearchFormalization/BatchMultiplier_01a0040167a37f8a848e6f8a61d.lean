import Mathlib

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_01a0040167a37f8a848e6f8a61d

/-! Pointwise nonvanishing multipliers cannot cancel the transverse coordinate. -/

def claim59495 : Prop :=
  ∀ (S : Set ℂ) (m : ℂ → ℂ) (a : ℝ → ℂ),
    (∀ z ∈ S, m z ≠ 0) →
    (∀ x : ℝ, a x = 0 ↔ x = 0) →
      ((∀ z ∈ S, m z * a (2 * z.re - 1) = 0) ↔
        ∀ z ∈ S, z.re = 1 / 2)

/-! Strict-horizon growth obstruction. -/

def claim59729 : Prop :=
  ∀ (P : ℝ → ℝ) (F : ℂ → ℂ) (z : ℂ),
    P 0 ≠ 0 → F z = 0 → z.im ≠ 0 →
      ∃ H : ℕ → ℝ → ℝ,
        (∀ N q, H N q > 0) ∧
        (∀ N y, H N (P (-y) / P 0) ≥ 0) ∧
        (∀ N, Continuous (H N)) ∧
        (∀ N, ¬ (∀ q₁ q₂ : ℝ, H N q₁ = H N q₂)) ∧
        (∀ N q, H N q < H (N + 1) q)


end MathlibPlus.Open.ResearchFormalization.Batch_01a0040167a37f8a848e6f8a61d
