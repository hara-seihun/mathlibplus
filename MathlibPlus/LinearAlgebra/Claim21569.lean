import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim21569

/-! The source claim's fixed-wedge edge spaces and Reynolds operators are
represented here by finite real matrices.  The theorem retains the exact
self-adjoint-projection Gram identity; the source-specific cube carriers and
Walsh description are not silently introduced. -/

open scoped BigOperators
open Matrix

/-- The finite-coordinate Gram energy identity underlying the fixed-wedge
operator: a self-adjoint idempotent `E` turns `Lᵀ E L` into the squared
energy of `E L q`. -/
theorem gramEnergy_identity_claim21569
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : Matrix ι κ ℝ) (E : Matrix ι ι ℝ)
    (q : κ → ℝ) (d : ℕ)
    (hEself : E.transpose = E)
    (hEproj : E * E = E) :
    let w := E *ᵥ (L *ᵥ q)
    q ⬝ᵥ (((2 : ℝ)⁻¹) ^ d • (L.transpose *ᵥ w)) =
      ((2 : ℝ)⁻¹) ^ d * (w ⬝ᵥ w) := by
  dsimp
  let v := L *ᵥ q
  let w := E *ᵥ v
  have hfixed : E *ᵥ w = w := by
    dsimp [w]
    rw [Matrix.mulVec_mulVec, hEproj]
  have hL : q ⬝ᵥ (L.transpose *ᵥ w) = w ⬝ᵥ v := by
    dsimp [v]
    exact Matrix.dotProduct_transpose_mulVec L q w
  have hE : v ⬝ᵥ w = w ⬝ᵥ w := by
    calc
      v ⬝ᵥ w = v ⬝ᵥ (E.transpose *ᵥ w) := by rw [hEself, hfixed]
      _ = w ⬝ᵥ (E *ᵥ v) := Matrix.dotProduct_transpose_mulVec E v w
      _ = w ⬝ᵥ w := rfl
  have henergy : q ⬝ᵥ (L.transpose *ᵥ w) = w ⬝ᵥ w := by
    rw [hL, dotProduct_comm, hE]
  calc
    q ⬝ᵥ (((2 : ℝ)⁻¹) ^ d • (L.transpose *ᵥ w)) =
        ((2 : ℝ)⁻¹) ^ d * (q ⬝ᵥ (L.transpose *ᵥ w)) := by
          simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = ((2 : ℝ)⁻¹) ^ d * (w ⬝ᵥ w) := by rw [henergy]

end MathlibPlus.LinearAlgebra.Claim21569
