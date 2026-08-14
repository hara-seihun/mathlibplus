import Mathlib

namespace MathlibPlus.Open

def left_and_right_tensor_lengthening_claim5282 : Prop :=
  let PosNat := {n : ℕ // 0 < n}
  let E := PosNat →₀ ℚ
  let e : PosNat → E := fun i => Finsupp.single i 1
  let shift : PosNat → PosNat :=
    fun i => ⟨i.1 + 1, Nat.succ_pos i.1⟩
  let S : E →ₗ[ℚ] E :=
    Finsupp.linearCombination ℚ (fun i => e (shift i))
  let left : TensorProduct ℚ E E →ₗ[ℚ] TensorProduct ℚ E E :=
    TensorProduct.map S LinearMap.id
  let right : TensorProduct ℚ E E →ₗ[ℚ] TensorProduct ℚ E E :=
    TensorProduct.map LinearMap.id S
  ∀ (i j : PosNat),
    left (TensorProduct.tmul ℚ (e i) (e j)) =
        TensorProduct.tmul ℚ (e (shift i)) (e j) ∧
      right (TensorProduct.tmul ℚ (e i) (e j)) =
        TensorProduct.tmul ℚ (e i) (e (shift j))

end MathlibPlus.Open
