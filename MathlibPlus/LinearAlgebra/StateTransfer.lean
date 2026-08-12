import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace MathlibPlus.LinearAlgebra.StateTransfer

/-- Claim 8642: the displayed state-transfer matrix has determinant one. -/
theorem stateTransferMatrix_det_claim8642 {K : Type*} [Field K] (a x : K) (ha : a ≠ 0) :
    (!![x / a, -a; 1 / a, 0] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  simp [Matrix.det_fin_two, ha]

/-- Claim 8642: the displayed matrix sends the state
`(a p, p_prev)` to `(a_next p_next, p)` exactly when the scalar recurrence
`a_next * p_next = x * p - a * p_prev` holds. -/
theorem stateTransferMatrix_transfer_claim8642 {K : Type*} [Field K]
    (a_next a x p_next p_prev p : K) (ha : a ≠ 0) :
    (![a_next * p_next, p] : Fin 2 → K) =
      Matrix.mulVec (!![x / a, -a; 1 / a, 0] : Matrix (Fin 2) (Fin 2) K)
        ![a * p, p_prev] ↔
    a_next * p_next = x * p - a * p_prev := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h0' : a_next * p_next = x / a * (a * p) + -(a * p_prev) := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, ha] using h0
    calc
      a_next * p_next = x / a * (a * p) + -(a * p_prev) := h0'
      _ = x * p - a * p_prev := by field_simp [ha]; ring
  · intro h
    funext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, ha, h]
      field_simp [ha]
      ring
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, ha]

end MathlibPlus.LinearAlgebra.StateTransfer
