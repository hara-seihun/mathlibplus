import Mathlib

noncomputable section

open scoped BigOperators

namespace MathlibPlus.Open.Research

def reciprocalProduct963 {N : ℕ} (α : Fin N → ℝ) (z : ℝ) : ℝ :=
  ∏ i : Fin N, (1 + α i * z)

def reciprocalD7_963 {N : ℕ} (α : Fin N → ℝ) : ℝ :=
  Matrix.det (fun i j : Fin 7 =>
    iteratedDeriv (6 + (j : ℕ) - (i : ℕ)) (reciprocalProduct963 α) 0)

/-- Admitted Claim 963, including its equality characterization. -/
def claim963 : Prop :=
  ∀ (N : ℕ), N ≤ 7 →
    ∀ (α : Fin N → ℝ),
      (∀ i, 0 ≤ α i) →
        0 ≤ reciprocalD7_963 α ∧
          (reciprocalD7_963 α = 0 ↔
            ∃ S : Finset (Fin N),
              (∀ i, i ∈ S ↔ 0 < α i) ∧ S.card ≤ 5) ∧
          (0 < reciprocalD7_963 α ↔
            ∃ S : Finset (Fin N),
              (∀ i, i ∈ S ↔ 0 < α i) ∧ 6 ≤ S.card)

end MathlibPlus.Open.Research
