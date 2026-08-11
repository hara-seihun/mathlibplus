import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Tactic

namespace MathlibPlus.LinearAlgebra

/-- Claim 53172: the displayed coefficient matrix of the reflection
`p(x) ↦ p(s - x)` is an involution. -/
theorem polynomialReflectionMatrixInvolution (s : ℝ) :
    let T : Matrix (Fin 3) (Fin 3) ℝ := !![
      1, 0, 0;
      s, -1, 0;
      s ^ 2, -2 * s, 1]
    T * T = 1 := by
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- Claim 53172: exchanging the two three-channel blocks with the same
reflection matrix is an involution. -/
theorem blockExchangeInvolution (s : ℝ) :
    let T : Matrix (Fin 3) (Fin 3) ℝ := !![
      1, 0, 0;
      s, -1, 0;
      s ^ 2, -2 * s, 1]
    let B : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
      Matrix.fromBlocks 0 T T 0
    B * B = 1 := by
  dsimp
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.fromBlocks, Fin.sum_univ_three] <;> ring

end MathlibPlus.LinearAlgebra

namespace MathlibPlus.Open.LinearAlgebra

/-- Claim 53172: the complete six-channel reflection statement, including
its nonnegative-majorant spectral-radius obstruction.  The `Fin 3 ⊕ Fin 3`
index is the two three-channel blocks. -/
def polynomialSixChannelReflection : Prop :=
  ∀ (s : ℝ),
    let T : Matrix (Fin 3) (Fin 3) ℝ := !![
      1, 0, 0;
      s, -1, 0;
      s ^ 2, -2 * s, 1]
    let B : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
      Matrix.fromBlocks 0 T T 0
    T * T = 1 ∧
      B * B = 1 ∧
      ∀ A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ,
        (∀ i j, 0 ≤ A i j ∧ |B i j| ≤ A i j) →
          1 ≤ spectralRadius ℝ A

end MathlibPlus.Open.LinearAlgebra
