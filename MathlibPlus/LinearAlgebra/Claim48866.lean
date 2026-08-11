import MathlibPlus.Basic

open scoped Matrix

namespace MathlibPlus.LinearAlgebra.Claim48866

/-- Summing clone coordinates pulls a class-level quadratic form back by the
aggregation matrix. -/
theorem cloneOccupation_quadraticPullback_claim48866
    {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommSemiring R]
    (P : Matrix ι κ R) (K : Matrix ι ι R) (v : κ → R) :
    dotProduct v ((P.transpose * K * P).mulVec v) =
      dotProduct (P.mulVec v) (K.mulVec (P.mulVec v)) := by
  have hrow : v ᵥ* (P.transpose * K * P) = (P *ᵥ v) ᵥ* K ᵥ* P := by
    calc
      v ᵥ* (P.transpose * K * P) =
          v ᵥ* (P.transpose * (K * P)) := by rw [Matrix.mul_assoc]
      _ = (v ᵥ* P.transpose) ᵥ* (K * P) := by
        rw [Matrix.vecMul_vecMul]
      _ = (P *ᵥ v) ᵥ* (K * P) := by
        rw [Matrix.vecMul_transpose]
      _ = ((P *ᵥ v) ᵥ* K) ᵥ* P := by
        rw [Matrix.vecMul_vecMul]
  rw [Matrix.dotProduct_mulVec, hrow, Matrix.dotProduct_mulVec]
  rw [← Matrix.dotProduct_vecMul_transpose]
  rw [Matrix.vecMul_transpose]
  rw [dotProduct_comm]

end MathlibPlus.LinearAlgebra.Claim48866
