import Mathlib

namespace MathlibPlus.Algebra.Claim50893

/-- The two labelled permutation configurations of the repeated edge block have
signed weights `0` and `-4`, hence total balance `-4`. -/
theorem repeatedEdgeBlock_signedBalance :
    let R : Matrix (Fin 2) (Fin 2) ℤ := !![0, 2; 2, 0]
    let identityWeight : ℤ := R 0 0 * R 1 1
    let transpositionWeight : ℤ := -(R 0 1 * R 1 0)
    identityWeight = 0 ∧
      transpositionWeight = -4 ∧
      identityWeight + transpositionWeight = -4 ∧
      ¬ (0 < identityWeight) ∧ ¬ (0 < transpositionWeight) := by
  norm_num

end MathlibPlus.Algebra.Claim50893
