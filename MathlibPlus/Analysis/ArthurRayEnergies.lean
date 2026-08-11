import MathlibPlus.Basic

namespace MathlibPlus.Analysis.ArthurRayEnergies

/-!
The direct/reflected ray energy identity from admitted claim 11383.  The two
source quantities are kept as local `let`s in the theorem, so neither an
unstated global definition nor an extra domain hypothesis is introduced.
-/

/-- If `D(U, Φ) = exp U + exp (-U) - 2 cos Φ` and
`R(U, Φ) = exp U + exp (-U) + 2 cos Φ`, then
`2 R - D = exp U + exp (-U) + 6 cos Φ`. -/
theorem two_reflected_sub_direct (U Φ : ℝ) :
    let D : ℝ := Real.exp U + Real.exp (-U) - 2 * Real.cos Φ
    let R : ℝ := Real.exp U + Real.exp (-U) + 2 * Real.cos Φ
    2 * R - D = Real.exp U + Real.exp (-U) + 6 * Real.cos Φ := by
  dsimp
  ring

end MathlibPlus.Analysis.ArthurRayEnergies
