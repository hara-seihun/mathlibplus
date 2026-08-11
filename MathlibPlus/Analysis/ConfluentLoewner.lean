import Mathlib

namespace MathlibPlus.Analysis.ConfluentLoewner

/-- The order-`n` confluent negative Loewner matrix of a real function `H` at `x`.
The proof argument preserves the source domain `n ≥ 1`; it does not affect entries. -/
noncomputable def confluentNegativeLoewnerMatrix
    (H : ℝ → ℝ) (n : ℕ) (_hn : 1 ≤ n) (x : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    (-1 : ℝ) ^ (i.val + j.val + 1) *
      iteratedDeriv (i.val + j.val + 1) H x /
        (Nat.factorial (i.val + j.val + 1) : ℝ)

@[simp]
theorem confluentNegativeLoewnerMatrix_apply
    (H : ℝ → ℝ) (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (i j : Fin n) :
    confluentNegativeLoewnerMatrix H n hn x i j =
      (-1 : ℝ) ^ (i.val + j.val + 1) *
        iteratedDeriv (i.val + j.val + 1) H x /
          (Nat.factorial (i.val + j.val + 1) : ℝ) := rfl

end MathlibPlus.Analysis.ConfluentLoewner
