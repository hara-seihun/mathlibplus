import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra.Claim4781

/-- The skew matrix obtained from the signed upper-triangular cut correlations. -/
def cutCorrelationSkewMatrix {C R : Type*} [Ring R] {n : ℕ}
    (s : C → Fin n → Fin n → R) (c : C) : Matrix (Fin n) (Fin n) R :=
  fun a b => if a < b then s c a b else if b < a then -s c b a else 0

theorem cutCorrelationSkewMatrix_transpose_neg {C R : Type*} [Ring R] {n : ℕ}
    (s : C → Fin n → Fin n → R) (c : C) :
    Matrix.transpose (cutCorrelationSkewMatrix s c) = -cutCorrelationSkewMatrix s c := by
  ext a b
  by_cases hab : a < b
  · have hba : ¬ b < a := by omega
    simp [cutCorrelationSkewMatrix, hab, hba]
  · by_cases hba : b < a
    · simp [cutCorrelationSkewMatrix, hab, hba]
    · have heq : a = b := by omega
      subst heq
      simp [cutCorrelationSkewMatrix]

end MathlibPlus.LinearAlgebra.Claim4781
