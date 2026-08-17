import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchBatch.R3642

noncomputable def completedRankThreeMatrix_claim51118 (moments : ℕ → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  let α : ℝ := 1 / 4
  let c : (ℕ → ℝ) → ℕ → ℝ :=
    fun m j => (-1 : ℝ) ^ j * m j
  let r : (ℕ → ℝ) → ℕ → ℝ :=
    fun m j =>
      ((j + 1 : ℕ) : ℝ) * (c m j + α * c m (j + 1))
  let b : (ℕ → ℝ) → ℕ → ℕ → ℝ :=
    fun m i j =>
      ∑ ℓ ∈ Finset.range (i + j + 2),
        ∑ k ∈ Finset.range (i + j + 2),
          if ℓ + k = i + j + 1 ∧
              ℓ < k ∧ ℓ ≤ i ∧ ℓ ≤ j ∧ i < k ∧ j < k then
            -((k - ℓ : ℕ) : ℝ) * c m ℓ * c m k
          else 0
  let K : (ℕ → ℝ) → Matrix (Fin 3) (Fin 3) ℝ :=
    fun m i j =>
      (1 / 2 : ℝ) * r m (i.val + j.val) +
        α ^ 2 * b m i.val j.val +
        α *
          ((if i.val = 0 then 0 else b m (i.val - 1) j.val) +
            (if j.val = 0 then 0 else b m i.val (j.val - 1))) +
        (if i.val = 0 ∨ j.val = 0 then 0
          else b m (i.val - 1) (j.val - 1)) -
        α * c m i.val * c m j.val
  K moments

end MathlibPlus.Open.ResearchBatch.R3642
