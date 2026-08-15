import Mathlib

namespace MathlibPlus.Open

def exists_real_positivity_witness_with_nonreal_zero : Prop :=
  ∃ (P : ℝ → ℝ) (H : ℕ → ℝ → ℝ) (F : ℂ → ℂ),
    P 0 ≠ 0 ∧
      (∀ (N : ℕ) (y : ℝ), 0 ≤ H N (P (-y) / P 0)) ∧
      ∃ z : ℂ, F z = 0 ∧ z.im ≠ 0

end MathlibPlus.Open
