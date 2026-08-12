import Mathlib

namespace MathlibPlus.Analysis.Claim44229

/-- Exact two-Rademacher obstruction from R-2914.  The coefficient vectors
`O₁` and `O₂` are the two depth-one Boolean coordinate trees; `A` is the
source's minimum of the two first-query posterior-variance costs for
`u = a O₁ + b O₂`. -/
theorem optimalAreaNotQuasiconvex :
    let O₁ : Fin 2 → ℚ := ![1, 0]
    let O₂ : Fin 2 → ℚ := ![0, 1]
    let A : (Fin 2 → ℚ) → ℚ := fun u =>
      min (u 0 ^ 2 + 2 * (u 1) ^ 2) (2 * (u 0) ^ 2 + (u 1) ^ 2)
    let f : Fin 2 → ℚ := (3 / 5 : ℚ) • O₁ + (2 / 5 : ℚ) • O₂
    let g : Fin 2 → ℚ := (2 / 5 : ℚ) • O₁ + (3 / 5 : ℚ) • O₂
    let h : Fin 2 → ℚ := (1 / 2 : ℚ) • (f + g)
    A f = 17 / 25 ∧
      A g = 17 / 25 ∧
      A h = 3 / 4 ∧
      A h > max (A f) (A g) ∧
      ¬ (∀ t : ℚ, 0 ≤ t → t ≤ 1 →
        A (t • f + (1 - t) • g) ≤ max (A f) (A g)) := by
  dsimp
  constructor
  · norm_num [min_def]
  constructor
  · norm_num [min_def]
  constructor
  · norm_num [min_def]
  constructor
  · norm_num [min_def]
  · intro hq
    have hhalf := hq (1 / 2 : ℚ) (by norm_num) (by norm_num)
    norm_num [min_def] at hhalf

end MathlibPlus.Analysis.Claim44229
