import Mathlib

namespace MathlibPlus.Algebra.Claim12288

/--
The rank-degree Euler-pairing matrix and its (unnormalized) symmetric part.
The source claim's additional parity assertion about topological periodic cyclic
homology is outside this elementary matrix formalization.
-/
theorem eulerPairingMatrix_symmetricPart_not_strictlyPositive_claim12288
    (g : ℕ) (r d r' d' : ℝ) :
    let M : Matrix (Fin 2) (Fin 2) ℝ := !![1 - (g : ℝ), 1; -1, 0]
    let v : Fin 2 → ℝ := ![r, d]
    let w : Fin 2 → ℝ := ![r', d']
    let S : Matrix (Fin 2) (Fin 2) ℝ := M + M.transpose
    v ⬝ᵥ M.mulVec w = (1 - (g : ℝ)) * r * r' + r * d' - d * r' ∧
      S = !![2 * (1 - (g : ℝ)), 0; 0, 0] ∧
      ¬ (∀ x : Fin 2 → ℝ, x ≠ 0 → x ⬝ᵥ S.mulVec x > 0) := by
  dsimp
  constructor
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.transpose, Matrix.add_apply] <;> ring
  · intro h
    have hx : (![0, 1] : Fin 2 → ℝ) ≠ 0 := by
      intro hx
      have hlast := congrFun hx (1 : Fin 2)
      norm_num at hlast
    have hzero := h (![0, 1] : Fin 2 → ℝ) hx
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hzero

end MathlibPlus.Algebra.Claim12288
