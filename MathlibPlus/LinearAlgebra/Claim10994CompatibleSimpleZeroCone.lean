import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim10994

open scoped Matrix

/-- Claim 10994: the compatible two-by-two family has determinant `t^2`. -/
def compatibleFamily_det : Prop :=
  ∀ (t : ℝ),
    Matrix.det (!![t, 0; 1, t] : Matrix (Fin 2) (Fin 2) ℝ) = t ^ 2

/-- Claim 10994: at the compatible family's scalar zero, kernel and cokernel
both have one dimension. -/
def compatibleFamily_zero_kernel_cokernel : Prop :=
  let M : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
  Module.finrank ℝ (LinearMap.ker (Matrix.toLin' M)) = 1 ∧
    Module.finrank ℝ
        ((Fin 2 → ℝ) ⧸ LinearMap.range (Matrix.toLin' M)) = 1

/-- Claim 10994: the scalar zero family has four total kernel/cokernel
states. -/
def scalarFamily_zero_total_states : Prop :=
  let M : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 0]
  Module.finrank ℝ (LinearMap.ker (Matrix.toLin' M)) +
      Module.finrank ℝ
        ((Fin 2 → ℝ) ⧸ LinearMap.range (Matrix.toLin' M)) = 4

end MathlibPlus.LinearAlgebra.Claim10994
