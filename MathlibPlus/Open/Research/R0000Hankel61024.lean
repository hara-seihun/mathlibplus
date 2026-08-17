import Mathlib

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.Research.R0000Hankel61024

def moment (N : ℕ) (y : Fin N → ℝ) (k : ℕ) : ℝ :=
  ∑ a : Fin N, y a ^ k

def momentMatrix (N : ℕ) (y : Fin N → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    4 * moment N y (i.1 + j.1 + 1) -
      moment N y (i.1 + j.1 + 2)

def positiveSemidefiniteTwo (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ x : Fin 2 → ℝ,
    0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, x i * M i j * x j

def positiveDefiniteTwo (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ x : Fin 2 → ℝ, x ≠ 0 →
    0 < ∑ i : Fin 2, ∑ j : Fin 2, x i * M i j * x j

/-- Claim 61024: the exact two-by-two moment matrix, determinant expansion,
and positive-semidefinite/positive-definite support criterion. -/
def claim61024 : Prop :=
  ∀ (N : ℕ) (y : Fin N → ℝ),
    1 ≤ N → (∀ a : Fin N, 0 < y a ∧ y a < 4) →
      let L := momentMatrix N y
      positiveSemidefiniteTwo L ∧
        Matrix.det L =
          ∑ a : Fin N, ∑ b ∈ Finset.Ioi a,
            y a * (4 - y a) * y b * (4 - y b) * (y a - y b) ^ 2 ∧
          (positiveDefiniteTwo L ↔
            ∃ a b : Fin N, a ≠ b ∧ y a ≠ y b) ∧
            ((∃ a b : Fin N, a ≠ b ∧ y a ≠ y b) → 0 < Matrix.det L)

end MathlibPlus.Open.Research.R0000Hankel61024

end
