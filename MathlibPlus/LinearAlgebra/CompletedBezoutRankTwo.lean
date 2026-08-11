import Mathlib

namespace MathlibPlus.LinearAlgebra.CompletedBezout

open Matrix

/-- Exact rank-two completed Bezout determinant in the scale-free moment coordinates
`R = m₁²/(m₀m₂)` and `S = m₁m₃/m₂²`, with `hⱼ = mⱼ/(2j)!`. -/
theorem rankTwo_det_ratioIdentity
    (m0 m1 m2 m3 : ℝ) (hm0 : m0 ≠ 0) (hm2 : m2 ≠ 0) :
    let C : Matrix (Fin 2) (Fin 2) ℝ :=
      !![m0 * (m1 / 2), 2 * m0 * (m2 / 24);
         2 * m0 * (m2 / 24), 3 * m0 * (m3 / 720) + (m1 / 2) * (m2 / 24)]
    let R := m1 ^ 2 / (m0 * m2)
    let S := m1 * m3 / m2 ^ 2
    det C = m0 ^ 2 * m2 ^ 2 / 1440 * (3 * S + 15 * R - 10) := by
  dsimp only
  rw [det_fin_two]
  norm_num
  field_simp
  ring

end MathlibPlus.LinearAlgebra.CompletedBezout
