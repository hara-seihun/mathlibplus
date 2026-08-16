import Mathlib

open Filter

namespace MathlibPlus.Open.Research.O0251

/-- Quasi-uniform selection from the half-period grid, with d indexed by L. -/
def quasiUniformSelectionFromDiniGrid : Prop :=
  ∀ (A B : ℝ) (d : ℝ → ℕ),
    A < B →
    Tendsto (fun L : ℝ => (d L : ℝ) / L) atTop (nhds 0) →
    ∀ᶠ L : ℝ in atTop,
      ∃ t : Fin (d L + 1) → ℝ,
        (∀ i, A ≤ t i ∧ t i ≤ B ∧
          ∃ m : ℤ, t i = ((m : ℝ) + (1 / 2 : ℝ)) * Real.pi / L) ∧
        (∀ i j, i.val < j.val →
          t i < t j ∧
          t j - t i ≥
            (B - A) / (4 * (d L : ℝ)) * ((j.val - i.val : ℕ) : ℝ))

end MathlibPlus.Open.Research.O0251
