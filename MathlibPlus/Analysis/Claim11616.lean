import Mathlib

namespace MathlibPlus.Analysis.Claim11616

/-- The two opposite two-mode Fourier vectors have identical diagonal
Parseval energies but different coherent cusp sums. -/
theorem positiveHorizontalEnergyLosesCuspPhase :
    let plus : Fin 2 → ℝ := ![1, 1]
    let minus : Fin 2 → ℝ := ![1, -1]
    let energy : (Fin 2 → ℝ) → Fin 2 → ℝ := fun v i => v i ^ 2
    let cusp : (Fin 2 → ℝ) → ℝ := fun v => ∑ i, v i
    energy plus = energy minus ∧
      cusp plus = 2 ∧
      cusp minus = 0 ∧
      ∀ w : Fin 2 → ℝ, 0 < w 0 → 0 < w 1 →
        (∑ i, w i * energy plus i) = ∑ i, w i * energy minus i := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext i
    fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_two]
  · norm_num [Fin.sum_univ_two]
  · intro w _hw0 _hw1
    congr 1
    funext i
    fin_cases i <;> norm_num

end MathlibPlus.Analysis.Claim11616
