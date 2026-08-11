import Mathlib

namespace MathlibPlus.AutomorphicReflectedCone

/-- At `n = 2`, the Ramanujan value `τ(2) = -24` gives the exact direct,
reflected, and cone margins recorded in C-0018. The split coefficient `e`,
compact coefficient `r`, and primitive zero-weight coefficient `z` are expanded
inline so that the normalization is auditable. -/
theorem exactMarginsAtTwo :
    let q : ℚ := 2 ^ 11
    let tau : ℚ := -24
    let e : ℚ := q + 1 + q⁻¹
    let r : ℚ := tau ^ 2 / q - 1
    let z : ℚ := 1
    let D : ℚ := e - r
    let R : ℚ := e + r - 2 * z
    let C : ℚ := e + 3 * r - 4 * z
    D = 4197825 / 2048 ∧
      R = 4190785 / 2048 ∧
      C = 4183745 / 2048 := by
  norm_num

end MathlibPlus.AutomorphicReflectedCone
