import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra.Claim29655

variable {K σ υ : Type*} [Field K]
  [Fintype σ] [Fintype υ] [DecidableEq σ] [DecidableEq υ]

/-- If the pivot block has a left inverse, multiplying a family of residual
matrices by that block does not change their common kernel.  Together with the
existing Schur-cancellation identity, this is the common-kernel half of claim
29655's diagonal-commutator formulation. -/
theorem commonKernel_diagonalCommutators_claim29655
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A_S Ainv : Matrix σ σ K) (Kmat : Matrix σ υ K)
    (d_S : κ → σ → K) (d_U : κ → υ → K)
    (x : υ → K) (hleft : Ainv * A_S = 1) :
    (∀ k, (A_S * (Kmat * Matrix.diagonal (d_U k) -
        Matrix.diagonal (d_S k) * Kmat)).mulVec x = 0) ↔
      ∀ k, (Kmat * Matrix.diagonal (d_U k) -
        Matrix.diagonal (d_S k) * Kmat).mulVec x = 0 := by
  constructor
  · intro h k
    calc
      (Kmat * Matrix.diagonal (d_U k) - Matrix.diagonal (d_S k) * Kmat).mulVec x =
          ((1 : Matrix σ σ K) * (Kmat * Matrix.diagonal (d_U k) -
            Matrix.diagonal (d_S k) * Kmat)).mulVec x := by
            rw [Matrix.one_mul]
      _ = ((Ainv * A_S) * (Kmat * Matrix.diagonal (d_U k) -
        Matrix.diagonal (d_S k) * Kmat)).mulVec x := by
            rw [hleft]
      _ = (Ainv * (A_S * (Kmat * Matrix.diagonal (d_U k) -
        Matrix.diagonal (d_S k) * Kmat))).mulVec x := by
            rw [Matrix.mul_assoc]
      _ = Ainv.mulVec ((A_S * (Kmat * Matrix.diagonal (d_U k) -
        Matrix.diagonal (d_S k) * Kmat)).mulVec x) := by
            rw [Matrix.mulVec_mulVec]
      _ = Ainv.mulVec 0 := by rw [h k]
      _ = 0 := Matrix.mulVec_zero _
  · intro h k
    rw [← Matrix.mulVec_mulVec, h k, Matrix.mulVec_zero]

end MathlibPlus.LinearAlgebra.Claim29655
