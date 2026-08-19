import Mathlib

namespace MathlibPlus.Open.LinearAlgebra.Claim2870

/-- Claim 2870: the displayed strictly totally positive rank-two matrix has a
negative alternating determinant, while its even scalar compression is
strictly larger than one half. -/
def sharpRankTwoCrossing_claim2870 : Prop :=
  let B : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 2]
  let D : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
  let R : Matrix (Fin 2) (Fin 2) ℝ := B * (1 + B)⁻¹
  let C : ℝ := R 1 1
  (0 < B 0 0 ∧ 0 < B 0 1 ∧ 0 < B 1 0 ∧ 0 < B 1 1 ∧
      0 < Matrix.det B) ∧
    Matrix.det (1 + D * B) = -1 ∧
    C = 3 / 5 ∧
    C > 1 / 2

end MathlibPlus.Open.LinearAlgebra.Claim2870
